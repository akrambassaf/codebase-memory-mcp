/*
 * pass_pdg.c — Program-Dependence layers (CFG / CDG / REACHING_DEF).
 *
 * Opt-in per-function program-dependence graph built on top of the extracted
 * call graph, gated to full/advanced index modes (cbm_pdg_extraction_enabled(),
 * set by the pipeline the same way macro extraction is). Skips taint: taint is
 * interprocedural and language-modelled; these three layers are intra-procedural
 * and structural.
 *
 * Layer 1  CFG          : BasicBlock nodes + CFG edges (reason: seq /
 *                         cond-true / cond-false / loop-back).
 * Layer 2  CDG          : Ferrante control dependence (post-dominators).
 *                         reason = branch sense 'T' | 'F'; guard=true when the
 *                         dependent block is an early exit (return/throw/...).
 * Layer 3  REACHING_DEF : GEN/KILL def->use data dependence, one variable per
 *                         pass; reason = variable name.
 *
 * Currently implemented for Tcl (OpenACS/AOLServer) only — statement kinds and
 * definition forms (proc / ad_proc) follow extract_tcl_ad_proc. Adding a
 * language means adding its statement classifier + body extraction, not
 * touching the solvers.
 *
 * Guards (per function, mirrors GitNexus --pdg caps):
 *   CBM_PDG_MAX_FN_LINES  skip functions longer than this
 *   CBM_PDG_MAX_BB        skip functions with more blocks
 *   CBM_PDG_MAX_CFG_EDGES CFG edge budget
 *   CBM_PDG_MAX_RD_VARS   REACHING_DEF variable budget
 *   CBM_PDG_MAX_RD_EDGES  REACHING_DEF edge budget
 */
#include "foundation/constants.h"
#include "pipeline/pipeline.h"
#include "pipeline/pipeline_internal.h"
#include "graph_buffer/graph_buffer.h"
#include "foundation/log.h"
#include "foundation/platform.h"
#include "foundation/compat.h"
#include "foundation/compat_fs.h"
#include "foundation/arena.h"
#include "foundation/mem_core.h"
#include "store/store.h"
#include "cbm.h"
#include "helpers.h"
#include "lang_specs.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>

enum {
    CBM_PDG_MAX_FN_LINES = 5000,
    CBM_PDG_MAX_BB = 1024,
    CBM_PDG_MAX_CFG_EDGES = 4096,
    CBM_PDG_MAX_RD_VARS = 128,
    CBM_PDG_MAX_RD_EDGES = 2048,
};

typedef enum {
    BB_PLAIN = 0, /* straight-line statements */
    BB_COND,      /* branch/loop predicate */
    BB_TERM,      /* ends in return/throw/error/break/continue */
    BB_EXIT,      /* synthetic function exit (bb 0) */
} bb_kind_t;

enum { EDGE_SEQ = 0, EDGE_TRUE = 1, EDGE_FALSE = 2, EDGE_BACK = 3 };

typedef struct {
    int start_line; /* 1-based; 0 for synthetic exit */
    int end_line;
    const char *name; /* arena: snippet */
    bb_kind_t kind;
    int succ[CBM_PDG_MAX_BB];
    uint8_t succ_kind[CBM_PDG_MAX_BB];
    int succ_n;
    int pred[CBM_PDG_MAX_BB];
    int pred_n;
    /* REACHING_DEF facts */
    char *set_vars[CBM_PDG_MAX_RD_VARS];
    int set_vars_n;
    char *use_vars[CBM_PDG_MAX_RD_VARS];
    int use_vars_n;
    /* postdom bitset (CBM_PDG_MAX_BB bits) */
    uint64_t pdom[(CBM_PDG_MAX_BB + 63) / 64];
    int64_t gbuf_id;
} pdg_bb_t;

typedef struct {
    CBMArena *arena;
    const char *source;
    const char *file_path;
    const char *project;
    const char *fn_qn;
    pdg_bb_t *bbs; /* arena: CBM_PDG_MAX_BB entries (heap — too large for the stack) */
    int bb_n;
    int cfg_edge_n;
    int rd_edge_n;
    CBMLanguage lang; /* statement syntax: CBM_LANG_TCL / CBM_LANG_PYTHON */
    /* loop context for break/continue (cond bb, post-loop join bb) */
    int loop_cond[CBM_PDG_MAX_BB];
    int loop_join[CBM_PDG_MAX_BB];
    int loop_n;
    bool overflow;
} pdg_fn_t;

typedef struct {
    int entry;
    int tail;
} pdg_region_t;

static const char *pdg_itoa(int val);

/* ── bitset helpers ────────────────────────────────────────────── */

static bool pdg_bit(const pdg_fn_t *f, int row, int col) {
    return (f->bbs[row].pdom[col / 64] >> (col % 64)) & 1U;
}
static void pdg_bit_set(pdg_fn_t *f, int row, int col) {
    f->bbs[row].pdom[col / 64] |= (1ULL << (col % 64));
}

/* ── model helpers ─────────────────────────────────────────────── */

static int pdg_new_bb(pdg_fn_t *f) {
    if (f->bb_n >= CBM_PDG_MAX_BB) {
        f->overflow = true;
        return -1;
    }
    int i = f->bb_n++;
    memset(&f->bbs[i], 0, sizeof(f->bbs[i]));
    return i;
}

static void pdg_link(pdg_fn_t *f, int from, int to, uint8_t kind) {
    if (from < 0 || to < 0 || from == to) {
        return;
    }
    pdg_bb_t *b = &f->bbs[from];
    if (b->succ_n >= CBM_PDG_MAX_BB) {
        f->overflow = true;
        return;
    }
    b->succ[b->succ_n] = to;
    b->succ_kind[b->succ_n] = kind;
    b->succ_n++;
    if (++f->cfg_edge_n > CBM_PDG_MAX_CFG_EDGES) {
        f->overflow = true;
    }
}

static char *pdg_text(pdg_fn_t *f, TSNode n) {
    return cbm_node_text(f->arena, n, f->source);
}

static char *pdg_snippet(pdg_fn_t *f, TSNode n) {
    char *raw = pdg_text(f, n);
    if (!raw) {
        return "";
    }
    char *nl = strchr(raw, '\n');
    if (nl) {
        *nl = '\0';
    }
    return raw;
}

static char *pdg_head_word(pdg_fn_t *f, TSNode n) {
    TSNode name = ts_node_child_by_field_name(n, TS_FIELD("name"));
    if (ts_node_is_null(name)) {
        return NULL;
    }
    return pdg_text(f, name);
}

static void pdg_append_stmt(pdg_fn_t *f, int bb, TSNode n) {
    pdg_bb_t *b = &f->bbs[bb];
    int sl = (int)ts_node_start_point(n).row + 1;
    int el = (int)ts_node_end_point(n).row + 1;
    if (b->start_line == 0 || sl < b->start_line) {
        b->start_line = sl;
        b->name = pdg_snippet(f, n);
    }
    if (el > b->end_line) {
        b->end_line = el;
    }
}

/* ── statement classification (Tcl / Python) ───────────────────── */

typedef enum {
    ST_PLAIN = 0,
    ST_IF,
    ST_WHILE,  /* while / foreach / for */
    ST_TRY,
    ST_TERM, /* return/break/continue/throw/error/raise */
    ST_SET,  /* def site: Tcl `set`, Python assignment */
} st_kind_t;

static st_kind_t pdg_classify(pdg_fn_t *f, TSNode n) {
    const char *t = ts_node_type(n);
    if (f->lang == CBM_LANG_PHP) {
        if (strcmp(t, "expression_statement") == 0) {
            TSNode inner = ts_node_named_child(n, 0);
            if (!ts_node_is_null(inner)) {
                const char *it = ts_node_type(inner);
                if (strcmp(it, "assignment_expression") == 0 ||
                    strcmp(it, "augmented_assignment_expression") == 0 ||
                    strcmp(it, "update_expression") == 0) {
                    return ST_SET;
                }
            }
            return ST_PLAIN;
        }
        if (strcmp(t, "if_statement") == 0) {
            return ST_IF;
        }
        if (strcmp(t, "while_statement") == 0 || strcmp(t, "for_statement") == 0 ||
            strcmp(t, "foreach_statement") == 0 || strcmp(t, "do_statement") == 0) {
            return ST_WHILE;
        }
        if (strcmp(t, "try_statement") == 0) {
            return ST_TRY;
        }
        if (strcmp(t, "return_statement") == 0 || strcmp(t, "break_statement") == 0 ||
            strcmp(t, "continue_statement") == 0 || strcmp(t, "throw_statement") == 0) {
            return ST_TERM;
        }
        if (strcmp(t, "assignment_expression") == 0 ||
            strcmp(t, "augmented_assignment_expression") == 0 ||
            strcmp(t, "update_expression") == 0) {
            return ST_SET;
        }
        return ST_PLAIN;
    }
    if (f->lang == CBM_LANG_PYTHON) {
        /* In a Python suite, assignments are wrapped in expression_statement
         * nodes. Unwrap so def sites are classified as ST_SET. */
        if (strcmp(t, "expression_statement") == 0) {
            TSNode inner = ts_node_named_child(n, 0);
            if (!ts_node_is_null(inner)) {
                const char *it = ts_node_type(inner);
                if (strcmp(it, "assignment") == 0 || strcmp(it, "augmented_assignment") == 0 ||
                    strcmp(it, "named_expression") == 0) {
                    return ST_SET;
                }
            }
            return ST_PLAIN;
        }
        if (strcmp(t, "if_statement") == 0) {
            return ST_IF;
        }
        if (strcmp(t, "while_statement") == 0 || strcmp(t, "for_statement") == 0) {
            return ST_WHILE;
        }
        if (strcmp(t, "try_statement") == 0) {
            return ST_TRY;
        }
        if (strcmp(t, "return_statement") == 0 || strcmp(t, "break_statement") == 0 ||
            strcmp(t, "continue_statement") == 0 || strcmp(t, "raise_statement") == 0) {
            return ST_TERM;
        }
        if (strcmp(t, "assignment") == 0 || strcmp(t, "augmented_assignment") == 0 ||
            strcmp(t, "named_expression") == 0) {
            return ST_SET;
        }
        return ST_PLAIN;
    }
    /* Tcl */
    if (strcmp(t, "if") == 0) {
        return ST_IF;
    }
    if (strcmp(t, "while") == 0 || strcmp(t, "foreach") == 0) {
        return ST_WHILE;
    }
    if (strcmp(t, "try") == 0) {
        return ST_TRY;
    }
    if (strcmp(t, "set") == 0) {
        return ST_SET;
    }
    char *w = pdg_head_word(f, n);
    if (!w) {
        return ST_PLAIN;
    }
    if (strcmp(w, "return") == 0 || strcmp(w, "break") == 0 ||
        strcmp(w, "continue") == 0 || strcmp(w, "throw") == 0 ||
        strcmp(w, "error") == 0) {
        return ST_TERM;
    }
    if (strcmp(w, "for") == 0) {
        return ST_WHILE; /* for init cond step body — handled like while */
    }
    return ST_PLAIN;
}

static bool pdg_is_stmt_node(const pdg_fn_t *f, TSNode n) {
    const char *t = ts_node_type(n);
    if (f->lang == CBM_LANG_PHP) {
        return strcmp(t, "expression_statement") == 0 ||
               strcmp(t, "assignment_expression") == 0 ||
               strcmp(t, "augmented_assignment_expression") == 0 ||
               strcmp(t, "update_expression") == 0 || strcmp(t, "if_statement") == 0 ||
               strcmp(t, "while_statement") == 0 || strcmp(t, "for_statement") == 0 ||
               strcmp(t, "foreach_statement") == 0 || strcmp(t, "do_statement") == 0 ||
               strcmp(t, "switch_statement") == 0 || strcmp(t, "try_statement") == 0 ||
               strcmp(t, "return_statement") == 0 || strcmp(t, "break_statement") == 0 ||
               strcmp(t, "continue_statement") == 0 || strcmp(t, "throw_statement") == 0 ||
               strcmp(t, "echo_statement") == 0 || strcmp(t, "global_declaration") == 0 ||
               strcmp(t, "static_variable_declaration") == 0 ||
               strcmp(t, "unset_statement") == 0 || strcmp(t, "goto_statement") == 0 ||
               strcmp(t, "function_definition") == 0 || strcmp(t, "method_declaration") == 0 ||
               strcmp(t, "class_declaration") == 0 || strcmp(t, "interface_declaration") == 0;
    }
    if (f->lang == CBM_LANG_PYTHON) {
        /* block children of a Python suite. Decorated/nested defs are PLAIN
         * statements (their own PDG is built separately by the def walk). */
        return strcmp(t, "expression_statement") == 0 || strcmp(t, "assignment") == 0 ||
               strcmp(t, "augmented_assignment") == 0 || strcmp(t, "if_statement") == 0 ||
               strcmp(t, "while_statement") == 0 || strcmp(t, "for_statement") == 0 ||
               strcmp(t, "try_statement") == 0 || strcmp(t, "with_statement") == 0 ||
               strcmp(t, "return_statement") == 0 || strcmp(t, "break_statement") == 0 ||
               strcmp(t, "continue_statement") == 0 || strcmp(t, "raise_statement") == 0 ||
               strcmp(t, "assert_statement") == 0 || strcmp(t, "pass_statement") == 0 ||
               strcmp(t, "delete_statement") == 0 || strcmp(t, "global_statement") == 0 ||
               strcmp(t, "nonlocal_statement") == 0 || strcmp(t, "import_statement") == 0 ||
               strcmp(t, "import_from_statement") == 0 || strcmp(t, "function_definition") == 0 ||
               strcmp(t, "class_definition") == 0 || strcmp(t, "decorated_definition") == 0;
    }
    /* Tcl */
    return strcmp(t, "command") == 0 || strcmp(t, "if") == 0 ||
           strcmp(t, "while") == 0 || strcmp(t, "foreach") == 0 ||
           strcmp(t, "try") == 0 || strcmp(t, "set") == 0 ||
           strcmp(t, "expr_cmd") == 0 || strcmp(t, "regexp") == 0 ||
           strcmp(t, "global") == 0;
}

/* ── body / statement extraction (Tcl / Python) ────────────────── */

static TSNode pdg_def_body(pdg_fn_t *f, TSNode def) {
    /* Python: function_definition -> body field (a block) */
    if (f->lang == CBM_LANG_PYTHON) {
        return ts_node_child_by_field_name(def, TS_FIELD("body"));
    }
    /* PHP: function_definition / method_declaration -> body field
     * (compound_statement); fallback to the last compound_statement child. */
    if (f->lang == CBM_LANG_PHP) {
        TSNode body = ts_node_child_by_field_name(def, TS_FIELD("body"));
        if (!ts_node_is_null(body)) {
            return body;
        }
        return cbm_find_child_by_kind(def, "compound_statement");
    }
    /* Tcl: procedure -> body field; ad_proc -> last word of arguments */
    TSNode body = ts_node_child_by_field_name(def, TS_FIELD("body"));
    if (!ts_node_is_null(body)) {
        return body;
    }
    TSNode wl = ts_node_child_by_field_name(def, TS_FIELD("arguments"));
    TSNode last = {0};
    if (!ts_node_is_null(wl)) {
        uint32_t wc = ts_node_child_count(wl);
        for (uint32_t i = 0; i < wc; i++) {
            TSNode w = ts_node_child(wl, i);
            const char *t = ts_node_type(w);
            if (strcmp(t, "word") == 0 || strcmp(t, "braced_word") == 0 ||
                strcmp(t, "quoted_word") == 0) {
                last = w;
            }
        }
    }
    return last;
}

/* Collect statement children of a body region. */
static int pdg_collect_stmts(pdg_fn_t *f, TSNode region, TSNode **out) {
    int n = 0;
    int cap = 16;
    TSNode *arr = cbm_arena_alloc(f->arena, (size_t)cap * sizeof(TSNode));
    if (!arr) {
        return 0;
    }
    uint32_t cc = ts_node_child_count(region);
    for (uint32_t i = 0; i < cc; i++) {
        TSNode c = ts_node_child(region, i);
        if (!pdg_is_stmt_node(f, c)) {
            continue;
        }
        if (n == cap) {
            cap *= 2;
            TSNode *big = cbm_arena_alloc(f->arena, (size_t)cap * sizeof(TSNode));
            if (!big) {
                return n;
            }
            memcpy(big, arr, (size_t)n * sizeof(TSNode));
            arr = big;
        }
        arr[n++] = c;
    }
    *out = arr;
    return n;
}

/* ── REACHING_DEF fact collection ──────────────────────────────── */

/* Collect every `identifier` text in the subtree of `root` into the use set.
 * Identifiers under the LEFT field of an assignment/augmented_assignment are
 * def sites, not uses, and are skipped (except via a separate def collect). */
static void pdg_py_collect_ids(pdg_fn_t *f, int bb, TSNode root, bool under_left) {
    pdg_bb_t *b = &f->bbs[bb];
    TSNode stack[64];
    bool flags[64];
    int top = 0;
    stack[top] = root;
    flags[top++] = under_left;
    while (top > 0 && b->use_vars_n < CBM_PDG_MAX_RD_VARS) {
        TSNode cur = stack[--top];
        bool ul = flags[top];
        const char *ct = ts_node_type(cur);
        if (strcmp(ct, "identifier") == 0 && !ul) {
            char *v = pdg_text(f, cur);
            if (v && v[0] && b->use_vars_n < CBM_PDG_MAX_RD_VARS) {
                bool dup = false;
                for (int j = 0; j < b->use_vars_n; j++) {
                    if (strcmp(b->use_vars[j], v) == 0) {
                        dup = true;
                        break;
                    }
                }
                if (!dup) {
                    b->use_vars[b->use_vars_n++] = v;
                }
            }
        }
        uint32_t cc = ts_node_child_count(cur);
        for (uint32_t i = 0; i < cc && top < (int)(sizeof(stack) / sizeof(stack[0])); i++) {
            TSNode c = ts_node_child(cur, i);
            bool child_left = ul;
            if (!child_left &&
                (strcmp(ct, "assignment") == 0 || strcmp(ct, "augmented_assignment") == 0)) {
                TSNode lf = ts_node_child_by_field_name(cur, TS_FIELD("left"));
                child_left = !ts_node_is_null(lf) &&
                             ts_node_start_byte(lf) == ts_node_start_byte(c) &&
                             ts_node_end_byte(lf) == ts_node_end_byte(c);
            }
            stack[top] = c;
            flags[top++] = child_left;
        }
    }
}

/* Add identifier names under `node` as DEF sites. */
static void pdg_py_collect_defs(pdg_fn_t *f, int bb, TSNode node) {
    pdg_bb_t *b = &f->bbs[bb];
    TSNode stack[64];
    int top = 0;
    stack[top++] = node;
    while (top > 0 && b->set_vars_n < CBM_PDG_MAX_RD_VARS) {
        TSNode cur = stack[--top];
        if (strcmp(ts_node_type(cur), "identifier") == 0) {
            char *v = pdg_text(f, cur);
            if (v && v[0] && b->set_vars_n < CBM_PDG_MAX_RD_VARS) {
                b->set_vars[b->set_vars_n++] = v;
            }
            continue;
        }
        uint32_t cc = ts_node_child_count(cur);
        for (uint32_t i = 0; i < cc && top < (int)(sizeof(stack) / sizeof(stack[0])); i++) {
            stack[top++] = ts_node_child(cur, i);
        }
    }
}

/* PHP: collect `$name` variable_name texts (minus the $) into the use set,
 * skipping identifiers under assignment/augmented_assignment LEFT fields. */
static void pdg_php_collect_ids(pdg_fn_t *f, int bb, TSNode root, bool under_left) {
    pdg_bb_t *b = &f->bbs[bb];
    TSNode stack[64];
    bool flags[64];
    int top = 0;
    stack[top] = root;
    flags[top++] = under_left;
    while (top > 0 && b->use_vars_n < CBM_PDG_MAX_RD_VARS) {
        TSNode cur = stack[--top];
        bool ul = flags[top];
        const char *ct = ts_node_type(cur);
        if (strcmp(ct, "variable_name") == 0 && !ul) {
            char *v = pdg_text(f, cur);
            if (v && v[0] == '$' && b->use_vars_n < CBM_PDG_MAX_RD_VARS) {
                bool dup = false;
                for (int j = 0; j < b->use_vars_n; j++) {
                    if (strcmp(b->use_vars[j], v + 1) == 0) {
                        dup = true;
                        break;
                    }
                }
                if (!dup) {
                    b->use_vars[b->use_vars_n++] = v + 1;
                }
            }
        }
        uint32_t cc = ts_node_child_count(cur);
        for (uint32_t i = 0; i < cc && top < (int)(sizeof(stack) / sizeof(stack[0])); i++) {
            TSNode c = ts_node_child(cur, i);
            bool child_left = ul;
            if (!child_left &&
                (strcmp(ct, "assignment_expression") == 0 ||
                 strcmp(ct, "augmented_assignment_expression") == 0)) {
                TSNode lf = ts_node_child_by_field_name(cur, TS_FIELD("left"));
                child_left = !ts_node_is_null(lf) &&
                             ts_node_start_byte(lf) == ts_node_start_byte(c) &&
                             ts_node_end_byte(lf) == ts_node_end_byte(c);
            }
            stack[top] = c;
            flags[top++] = child_left;
        }
    }
}

/* PHP: add variable_name names under `node` as DEF sites. */
static void pdg_php_collect_defs(pdg_fn_t *f, int bb, TSNode node) {
    pdg_bb_t *b = &f->bbs[bb];
    TSNode stack[64];
    int top = 0;
    stack[top++] = node;
    while (top > 0 && b->set_vars_n < CBM_PDG_MAX_RD_VARS) {
        TSNode cur = stack[--top];
        if (strcmp(ts_node_type(cur), "variable_name") == 0) {
            char *v = pdg_text(f, cur);
            if (v && v[0] == '$' && b->set_vars_n < CBM_PDG_MAX_RD_VARS) {
                b->set_vars[b->set_vars_n++] = v + 1;
            }
            continue;
        }
        uint32_t cc = ts_node_child_count(cur);
        for (uint32_t i = 0; i < cc && top < (int)(sizeof(stack) / sizeof(stack[0])); i++) {
            stack[top++] = ts_node_child(cur, i);
        }
    }
}

static void pdg_collect_facts(pdg_fn_t *f, int bb, TSNode n) {
    pdg_bb_t *b = &f->bbs[bb];
    const char *t = ts_node_type(n);
    if (f->lang == CBM_LANG_PHP) {
        /* unwrap expression_statement → assignment/update expression */
        if (strcmp(t, "expression_statement") == 0) {
            TSNode inner = ts_node_named_child(n, 0);
            if (!ts_node_is_null(inner)) {
                const char *it = ts_node_type(inner);
                if (strcmp(it, "assignment_expression") == 0 ||
                    strcmp(it, "augmented_assignment_expression") == 0 ||
                    strcmp(it, "update_expression") == 0) {
                    n = inner;
                    t = it;
                }
            }
        }
        if (strcmp(t, "assignment_expression") == 0) {
            TSNode left = ts_node_child_by_field_name(n, TS_FIELD("left"));
            TSNode right = ts_node_child_by_field_name(n, TS_FIELD("right"));
            if (!ts_node_is_null(left)) {
                pdg_php_collect_defs(f, bb, left);
            }
            if (!ts_node_is_null(right)) {
                pdg_php_collect_ids(f, bb, right, false);
            }
        } else if (strcmp(t, "augmented_assignment_expression") == 0) {
            TSNode left = ts_node_child_by_field_name(n, TS_FIELD("left"));
            TSNode right = ts_node_child_by_field_name(n, TS_FIELD("right"));
            if (!ts_node_is_null(left)) {
                pdg_php_collect_defs(f, bb, left);
                pdg_php_collect_ids(f, bb, left, false); /* $x += 1 reads $x too */
            }
            if (!ts_node_is_null(right)) {
                pdg_php_collect_ids(f, bb, right, false);
            }
        } else if (strcmp(t, "update_expression") == 0) {
            /* $x++ / ++$x: argument is a variable_name, def + use */
            TSNode arg = ts_node_child_by_field_name(n, TS_FIELD("argument"));
            if (!ts_node_is_null(arg)) {
                pdg_php_collect_defs(f, bb, arg);
                pdg_php_collect_ids(f, bb, arg, false);
            }
        } else {
            pdg_php_collect_ids(f, bb, n, false);
        }
        return;
    }
    if (f->lang == CBM_LANG_PYTHON) {
        /* unwrap expression_statement → assignment */
        if (strcmp(t, "expression_statement") == 0) {
            TSNode inner = ts_node_named_child(n, 0);
            if (!ts_node_is_null(inner)) {
                const char *it = ts_node_type(inner);
                if (strcmp(it, "assignment") == 0 || strcmp(it, "augmented_assignment") == 0 ||
                    strcmp(it, "named_expression") == 0) {
                    n = inner;
                    t = it;
                }
            }
        }
        if (strcmp(t, "assignment") == 0) {
            TSNode left = ts_node_child_by_field_name(n, TS_FIELD("left"));
            TSNode right = ts_node_child_by_field_name(n, TS_FIELD("right"));
            if (!ts_node_is_null(left)) {
                pdg_py_collect_defs(f, bb, left);
            }
            if (!ts_node_is_null(right)) {
                pdg_py_collect_ids(f, bb, right, false);
            }
        } else if (strcmp(t, "augmented_assignment") == 0) {
            TSNode left = ts_node_child_by_field_name(n, TS_FIELD("left"));
            TSNode right = ts_node_child_by_field_name(n, TS_FIELD("right"));
            if (!ts_node_is_null(left)) {
                pdg_py_collect_defs(f, bb, left);
                /* x += 1 also READS x — count the left side as a use too */
                pdg_py_collect_ids(f, bb, left, false);
            }
            if (!ts_node_is_null(right)) {
                pdg_py_collect_ids(f, bb, right, false);
            }
        } else if (strcmp(t, "named_expression") == 0) {
            TSNode nm = ts_node_child_by_field_name(n, TS_FIELD("name"));
            TSNode val = ts_node_child_by_field_name(n, TS_FIELD("value"));
            if (!ts_node_is_null(nm)) {
                pdg_py_collect_defs(f, bb, nm);
            }
            if (!ts_node_is_null(val)) {
                pdg_py_collect_ids(f, bb, val, false);
            }
        } else {
            pdg_py_collect_ids(f, bb, n, false);
        }
        return;
    }
    /* Tcl */
    if (strcmp(t, "set") == 0) {
        /* `set var value` — the "set" keyword is an anonymous token. The
         * variable is the `name` field when the grammar exposes one, else the
         * first named simple_word/id child. */
        TSNode name_node = ts_node_child_by_field_name(n, TS_FIELD("name"));
        if (ts_node_is_null(name_node) || strcmp(ts_node_type(name_node), "simple_word") != 0) {
            TSNode fallback = {0};
            uint32_t ncc = ts_node_named_child_count(n);
            for (uint32_t ci = 0; ci < ncc; ci++) {
                TSNode c = ts_node_named_child(n, ci);
                const char *ct = ts_node_type(c);
                if (strcmp(ct, "simple_word") == 0 || strcmp(ct, "id") == 0) {
                    fallback = c;
                    break;
                }
            }
            name_node = fallback;
        }
        if (!ts_node_is_null(name_node)) {
            char *v = pdg_text(f, name_node);
            if (v && v[0] && v[0] != '{' && b->set_vars_n < CBM_PDG_MAX_RD_VARS) {
                b->set_vars[b->set_vars_n++] = v;
            }
        }
    }
    /* $refs: explicit stack over the statement subtree (command/set/expr_cmd
     * all carry variable_substitution nodes in their words). */
    TSNode stack[64];
    int top = 0;
    stack[top++] = n;
    while (top > 0 && b->use_vars_n < CBM_PDG_MAX_RD_VARS) {
        TSNode cur = stack[--top];
        uint32_t cc = ts_node_child_count(cur);
        for (uint32_t i = 0; i < cc && b->use_vars_n < CBM_PDG_MAX_RD_VARS; i++) {
            TSNode c = ts_node_child(cur, i);
            const char *ct = ts_node_type(c);
            if (strcmp(ct, "variable_substitution") == 0) {
                char *v = pdg_text(f, c);
                if (v && v[0] == '$') {
                    b->use_vars[b->use_vars_n++] = v + 1;
                }
            } else if (strcmp(ct, "command") == 0 || strcmp(ct, "if") == 0 ||
                       strcmp(ct, "while") == 0 || strcmp(ct, "foreach") == 0 ||
                       strcmp(ct, "set") == 0 || strcmp(ct, "expr_cmd") == 0 ||
                       strcmp(ct, "try") == 0 || strcmp(ct, "regexp") == 0 ||
                       strcmp(ct, "command_substitution") == 0) {
                if (top < (int)(sizeof(stack) / sizeof(stack[0]))) {
                    stack[top++] = c;
                }
            }
        }
    }
}

/* Collect uses in a condition word (branch predicates). */
static void pdg_collect_cond_uses(pdg_fn_t *f, int bb, TSNode cond_word) {
    pdg_bb_t *b = &f->bbs[bb];
    if (f->lang == CBM_LANG_PHP) {
        pdg_php_collect_ids(f, bb, cond_word, false);
        return;
    }
    if (f->lang == CBM_LANG_PYTHON) {
        pdg_py_collect_ids(f, bb, cond_word, false);
        return;
    }
    TSNode stack[64];
    int top = 0;
    stack[top++] = cond_word;
    while (top > 0 && b->use_vars_n < CBM_PDG_MAX_RD_VARS) {
        TSNode cur = stack[--top];
        uint32_t cc = ts_node_child_count(cur);
        for (uint32_t i = 0; i < cc && b->use_vars_n < CBM_PDG_MAX_RD_VARS; i++) {
            TSNode c = ts_node_child(cur, i);
            if (strcmp(ts_node_type(c), "variable_substitution") == 0) {
                char *v = pdg_text(f, c);
                if (v && v[0] == '$') {
                    b->use_vars[b->use_vars_n++] = v + 1;
                }
            } else if (top < (int)(sizeof(stack) / sizeof(stack[0]))) {
                stack[top++] = c;
            }
        }
    }
}

/* ── CFG builder ───────────────────────────────────────────────── */

static pdg_region_t pdg_build_region(pdg_fn_t *f, TSNode *stmts, int n, int exit_bb);

/* Open a PLAIN bb for straight-line statements; links from cur. */
static int pdg_open_plain(pdg_fn_t *f, int cur) {
    if (cur >= 0 && f->bbs[cur].kind == BB_PLAIN && f->bbs[cur].start_line == 0) {
        return cur;
    }
    int b = pdg_new_bb(f);
    if (b < 0) {
        return -1;
    }
    f->bbs[b].kind = BB_PLAIN;
    if (cur >= 0) {
        pdg_link(f, cur, b, EDGE_SEQ);
    }
    return b;
}

/* while/foreach/for condition + body (language-aware). */
static TSNode pdg_loop_cond(pdg_fn_t *f, TSNode n) {
    TSNode cond = ts_node_child_by_field_name(n, TS_FIELD("condition"));
    if (!ts_node_is_null(cond)) {
        return cond;
    }
    /* Python for_statement: no condition; the iterable is the `right` field */
    if (f->lang == CBM_LANG_PYTHON) {
        return ts_node_child_by_field_name(n, TS_FIELD("right"));
    }
    if (f->lang == CBM_LANG_PHP) {
        /* PHP foreach/for: the iterable is typically the second named child of
         * the header; approximate with the second named child. */
        uint32_t ncc = ts_node_named_child_count(n);
        if (ncc >= 2) {
            return ts_node_named_child(n, 1);
        }
    }
    TSNode null_node = {0};
    return null_node;
}
static TSNode pdg_loop_body(pdg_fn_t *f, TSNode n) {
    TSNode cons = ts_node_child_by_field_name(n, TS_FIELD("consequence"));
    if (!ts_node_is_null(cons)) {
        return cons;
    }
    cons = ts_node_child_by_field_name(n, TS_FIELD("body"));
    if (!ts_node_is_null(cons)) {
        return cons;
    }
    if (f->lang == CBM_LANG_PHP) {
        /* PHP loop bodies are compound_statement children */
        return cbm_find_child_by_kind(n, "compound_statement");
    }
    if (f->lang == CBM_LANG_PYTHON) {
        TSNode null_node = {0};
        return null_node;
    }
    /* Tcl: the body is a DIRECT braced_word child with no field at all, so
     * fall back to the last braced/word child of the node itself; for a `for`
     * command it is the last word of the arguments word_list. */
    TSNode last = {0};
    uint32_t cc = ts_node_child_count(n);
    for (uint32_t i = 0; i < cc; i++) {
        TSNode w = ts_node_child(n, i);
        const char *t = ts_node_type(w);
        if (strcmp(t, "word") == 0 || strcmp(t, "braced_word") == 0 ||
            strcmp(t, "quoted_word") == 0) {
            last = w;
        }
    }
    if (!ts_node_is_null(last)) {
        return last;
    }
    /* `for` is a plain command: body = last word of the arguments word_list */
    TSNode wl = ts_node_child_by_field_name(n, TS_FIELD("arguments"));
    last = (TSNode){0};
    if (!ts_node_is_null(wl)) {
        uint32_t wc = ts_node_child_count(wl);
        for (uint32_t i = 0; i < wc; i++) {
            TSNode w = ts_node_child(wl, i);
            const char *t = ts_node_type(w);
            if (strcmp(t, "word") == 0 || strcmp(t, "braced_word") == 0 ||
                strcmp(t, "quoted_word") == 0) {
                last = w;
            }
        }
    }
    return last;
}

static int pdg_build_if(pdg_fn_t *f, TSNode if_node, int cur) {
    TSNode cond = ts_node_child_by_field_name(if_node, TS_FIELD("condition"));
    TSNode cons = ts_node_child_by_field_name(if_node, TS_FIELD("consequence"));
    TSNode alt = ts_node_child_by_field_name(if_node, TS_FIELD("alternative"));
    /* Else arm can be a direct CHILD node when the `alternative` field is
     * null: Tcl `else`, Python `else_clause`, PHP `else_clause`. */
    if (ts_node_is_null(alt)) {
        const char *else_t = (f->lang == CBM_LANG_PYTHON || f->lang == CBM_LANG_PHP)
                                 ? "else_clause"
                                 : "else";
        uint32_t icc0 = ts_node_child_count(if_node);
        for (uint32_t i = 0; i < icc0; i++) {
            TSNode c = ts_node_child(if_node, i);
            if (strcmp(ts_node_type(c), else_t) != 0) {
                continue;
            }
            if (f->lang == CBM_LANG_PYTHON || f->lang == CBM_LANG_PHP) {
                alt = ts_node_child_by_field_name(c, TS_FIELD("body"));
                if (ts_node_is_null(alt)) {
                    alt = cbm_find_child_by_kind(c, "compound_statement");
                }
                break;
            }
            uint32_t ecc = ts_node_child_count(c);
            for (uint32_t j = 0; j < ecc; j++) {
                TSNode w = ts_node_child(c, j);
                const char *t = ts_node_type(w);
                if (strcmp(t, "word") == 0 || strcmp(t, "braced_word") == 0 ||
                    strcmp(t, "quoted_word") == 0) {
                    alt = w;
                    break;
                }
            }
            if (!ts_node_is_null(alt)) {
                break;
            }
        }
    }

    int cond_bb = pdg_new_bb(f);
    if (cond_bb < 0) {
        return cur;
    }
    f->bbs[cond_bb].kind = BB_COND;
    f->bbs[cond_bb].start_line = (int)ts_node_start_point(if_node).row + 1;
    f->bbs[cond_bb].end_line = (int)ts_node_end_point(if_node).row + 1;
    f->bbs[cond_bb].name = "if";
    if (!ts_node_is_null(cond)) {
        pdg_collect_cond_uses(f, cond_bb, cond);
    }
    pdg_link(f, cur, cond_bb, EDGE_SEQ);

    /* tails of all arms that must join */
    int tails[16];
    int tails_n = 0;
    int last_cond = cond_bb;

    /* then arm */
    if (!ts_node_is_null(cons)) {
        TSNode *s = NULL;
        int sn = pdg_collect_stmts(f, cons, &s);
        pdg_region_t r = pdg_build_region(f, s, sn, -1);
        if (r.entry >= 0) {
            pdg_link(f, cond_bb, r.entry, EDGE_TRUE);
            if (tails_n < (int)(sizeof(tails) / sizeof(tails[0]))) {
                tails[tails_n++] = r.tail;
            }
        }
    } else {
        pdg_link(f, cond_bb, -1, EDGE_TRUE); /* empty then — joined below */
        tails[tails_n++] = cond_bb;
    }

    /* elseif chain: Tcl `elseif`, Python `elif_clause`, PHP `else_if_clause` */
    const char *elif_t = (f->lang == CBM_LANG_PYTHON)   ? "elif_clause"
                         : (f->lang == CBM_LANG_PHP) ? "else_if_clause"
                                                     : "elseif";
    uint32_t icc = ts_node_child_count(if_node);
    for (uint32_t i = 0; i < icc; i++) {
        TSNode c = ts_node_child(if_node, i);
        if (strcmp(ts_node_type(c), elif_t) != 0) {
            continue;
        }
        int e_cond = pdg_new_bb(f);
        if (e_cond < 0) {
            break;
        }
        f->bbs[e_cond].kind = BB_COND;
        f->bbs[e_cond].start_line = (int)ts_node_start_point(c).row + 1;
        f->bbs[e_cond].end_line = (int)ts_node_end_point(c).row + 1;
        f->bbs[e_cond].name = "elseif";
        TSNode econd = ts_node_child_by_field_name(c, TS_FIELD("condition"));
        if (!ts_node_is_null(econd)) {
            pdg_collect_cond_uses(f, e_cond, econd);
        }
        pdg_link(f, last_cond, e_cond, EDGE_FALSE);
        TSNode econs = pdg_loop_body(f, c); /* elseif: consequence field or body child */
        if (!ts_node_is_null(econs)) {
            TSNode *s = NULL;
            int sn = pdg_collect_stmts(f, econs, &s);
            pdg_region_t r = pdg_build_region(f, s, sn, -1);
            if (r.entry >= 0) {
                pdg_link(f, e_cond, r.entry, EDGE_TRUE);
                if (tails_n < (int)(sizeof(tails) / sizeof(tails[0]))) {
                    tails[tails_n++] = r.tail;
                }
            }
        } else if (tails_n < (int)(sizeof(tails) / sizeof(tails[0]))) {
            tails[tails_n++] = e_cond;
        }
        last_cond = e_cond;
    }

    /* else arm */
    if (!ts_node_is_null(alt)) {
        TSNode *s = NULL;
        int sn = pdg_collect_stmts(f, alt, &s);
        pdg_region_t r = pdg_build_region(f, s, sn, -1);
        if (r.entry >= 0) {
            pdg_link(f, last_cond, r.entry, EDGE_FALSE);
            if (tails_n < (int)(sizeof(tails) / sizeof(tails[0]))) {
                tails[tails_n++] = r.tail;
            }
        }
    } else if (tails_n < (int)(sizeof(tails) / sizeof(tails[0]))) {
        tails[tails_n++] = last_cond; /* fall-through cond-false = join */
    }

    int join = pdg_new_bb(f);
    if (join < 0) {
        return cur;
    }
    f->bbs[join].kind = BB_PLAIN;
    for (int ti = 0; ti < tails_n; ti++) {
        pdg_link(f, tails[ti], join, EDGE_SEQ);
    }
    return join;
}

static int pdg_build_loop(pdg_fn_t *f, TSNode n, int cur, const char *name) {
    TSNode cond = pdg_loop_cond(f, n);
    TSNode body = pdg_loop_body(f, n);

    int cond_bb = pdg_new_bb(f);
    if (cond_bb < 0) {
        return cur;
    }
    f->bbs[cond_bb].kind = BB_COND;
    f->bbs[cond_bb].start_line = (int)ts_node_start_point(n).row + 1;
    f->bbs[cond_bb].end_line = (int)ts_node_end_point(n).row + 1;
    f->bbs[cond_bb].name = name;
    if (!ts_node_is_null(cond)) {
        pdg_collect_cond_uses(f, cond_bb, cond);
    }
    pdg_link(f, cur, cond_bb, EDGE_SEQ);

    int join = pdg_new_bb(f);
    if (join < 0) {
        return cur;
    }
    f->bbs[join].kind = BB_PLAIN;

    /* loop context for break/continue inside the body */
    if (f->loop_n < CBM_PDG_MAX_BB) {
        f->loop_cond[f->loop_n] = cond_bb;
        f->loop_join[f->loop_n] = join;
        f->loop_n++;
    }
    if (!ts_node_is_null(body)) {
        TSNode *s = NULL;
        int sn = pdg_collect_stmts(f, body, &s);
        pdg_region_t r = pdg_build_region(f, s, sn, -1);
        if (r.entry >= 0) {
            pdg_link(f, cond_bb, r.entry, EDGE_TRUE);
            pdg_link(f, r.tail, cond_bb, EDGE_BACK);
        }
    }
    if (f->loop_n > 0) {
        f->loop_n--;
    }
    pdg_link(f, cond_bb, join, EDGE_FALSE);
    return join;
}

/* try body + catch/finally handlers, chained with seq (v1 approximation). */
static int pdg_build_try(pdg_fn_t *f, TSNode n, int cur) {
    uint32_t cc = ts_node_child_count(n);
    int first = cur;
    for (uint32_t i = 0; i < cc; i++) {
        TSNode c = ts_node_child(n, i);
        const char *t = ts_node_type(c);
        TSNode body = {0};
        if (f->lang == CBM_LANG_PHP) {
            /* PHP try_statement: body compound_statement, then each
             * catch_clause body, then finally_clause body. */
            if (strcmp(t, "compound_statement") == 0) {
                body = c;
            } else if (strcmp(t, "catch_clause") == 0 || strcmp(t, "finally_clause") == 0) {
                body = ts_node_child_by_field_name(c, TS_FIELD("body"));
                if (ts_node_is_null(body)) {
                    body = cbm_find_child_by_kind(c, "compound_statement");
                }
            }
        } else if (f->lang == CBM_LANG_PYTHON) {
            /* try_statement: chain its block children in order — the try body
             * block, then each except_clause's block, else, finally. */
            if (strcmp(t, "block") == 0) {
                body = c;
            } else if (strcmp(t, "except_clause") == 0 || strcmp(t, "else_clause") == 0 ||
                       strcmp(t, "finally_clause") == 0) {
                body = ts_node_child_by_field_name(c, TS_FIELD("body"));
                if (ts_node_is_null(body)) {
                    /* except_clause's suite is not fielded in tree-sitter-python */
                    body = cbm_find_child_by_kind(c, "block");
                }
            }
        } else if (strcmp(t, "catch") == 0 || strcmp(t, "finally") == 0) {
            body = ts_node_child_by_field_name(c, TS_FIELD("consequence"));
        } else if (strcmp(t, "word") == 0 || strcmp(t, "braced_word") == 0 ||
                   strcmp(t, "quoted_word") == 0) {
            body = c; /* Tcl: try's own body word */
        }
        if (ts_node_is_null(body)) {
            continue;
        }
        TSNode *s = NULL;
        int sn = pdg_collect_stmts(f, body, &s);
        if (sn == 0) {
            continue;
        }
        pdg_region_t r = pdg_build_region(f, s, sn, -1);
        if (r.entry < 0) {
            continue;
        }
        if (first == cur) {
            pdg_link(f, cur, r.entry, EDGE_SEQ);
            first = r.entry;
        } else {
            pdg_link(f, cur, r.entry, EDGE_SEQ);
        }
        cur = r.tail;
    }
    return (first == cur) ? pdg_open_plain(f, cur) : cur;
}

static pdg_region_t pdg_build_region(pdg_fn_t *f, TSNode *stmts, int n, int exit_bb) {
    pdg_region_t r;
    r.entry = -1;
    r.tail = -1;
    int cur = -1;
    for (int i = 0; i < n && !f->overflow; i++) {
        TSNode st = stmts[i];
        st_kind_t k = pdg_classify(f, st);
        switch (k) {
        case ST_PLAIN:
            cur = pdg_open_plain(f, cur);
            if (cur < 0) {
                return r;
            }
            pdg_append_stmt(f, cur, st);
            pdg_collect_facts(f, cur, st);
            r.tail = cur;
            break;
        case ST_SET:
            cur = pdg_open_plain(f, cur);
            if (cur < 0) {
                return r;
            }
            pdg_append_stmt(f, cur, st);
            pdg_collect_facts(f, cur, st);
            r.tail = cur;
            break;
        case ST_TERM: {
            int tb = pdg_new_bb(f);
            if (tb < 0) {
                return r;
            }
            f->bbs[tb].kind = BB_TERM;
            pdg_append_stmt(f, tb, st);
            pdg_collect_facts(f, tb, st);
            char *w = pdg_head_word(f, st);
            bool is_break = false;
            bool is_continue = false;
            if (f->lang == CBM_LANG_PYTHON || f->lang == CBM_LANG_PHP) {
                const char *tst = ts_node_type(st);
                is_break = strcmp(tst, "break_statement") == 0;
                is_continue = strcmp(tst, "continue_statement") == 0;
            } else {
                is_break = (w && strcmp(w, "break") == 0);
                is_continue = (w && strcmp(w, "continue") == 0);
            }
            if (cur >= 0) {
                pdg_link(f, cur, tb, EDGE_SEQ);
            }
            if (is_break && f->loop_n > 0) {
                pdg_link(f, tb, f->loop_join[f->loop_n - 1], EDGE_SEQ);
            } else if (is_continue && f->loop_n > 0) {
                pdg_link(f, tb, f->loop_cond[f->loop_n - 1], EDGE_BACK);
            } else if (exit_bb >= 0) {
                pdg_link(f, tb, exit_bb, EDGE_SEQ);
            }
            cur = -1;
            r.tail = tb;
            break;
        }
        case ST_IF:
            cur = pdg_build_if(f, st, cur >= 0 ? cur : pdg_open_plain(f, cur));
            r.tail = cur;
            break;
        case ST_WHILE: {
            const char *lname = "loop";
            if (f->lang == CBM_LANG_PYTHON) {
                lname = strcmp(ts_node_type(st), "for_statement") == 0 ? "for" : "while";
            } else if (f->lang == CBM_LANG_PHP) {
                const char *pt = ts_node_type(st);
                if (strcmp(pt, "while_statement") == 0) {
                    lname = "while";
                } else if (strcmp(pt, "for_statement") == 0) {
                    lname = "for";
                } else if (strcmp(pt, "foreach_statement") == 0) {
                    lname = "foreach";
                } else if (strcmp(pt, "do_statement") == 0) {
                    lname = "do";
                }
            } else {
                char *w = pdg_head_word(f, st);
                if (w) {
                    lname = w;
                }
            }
            cur = pdg_build_loop(f, st, cur >= 0 ? cur : pdg_open_plain(f, cur), lname);
            r.tail = cur;
            break;
        }
        case ST_TRY:
            cur = pdg_build_try(f, st, cur >= 0 ? cur : pdg_open_plain(f, cur));
            r.tail = cur;
            break;
        }
        if (r.entry < 0) {
            r.entry = r.tail;
        }
    }
    if (r.tail < 0) {
        /* empty region: a single empty bb */
        int b = pdg_open_plain(f, -1);
        r.entry = b;
        r.tail = b;
    }
    return r;
}

/* ── CDG: post-dominators + control dependence ─────────────────── */

static void pdg_compute_preds(pdg_fn_t *f) {
    for (int i = 0; i < f->bb_n; i++) {
        f->bbs[i].pred_n = 0;
    }
    for (int i = 0; i < f->bb_n; i++) {
        for (int s = 0; s < f->bbs[i].succ_n; s++) {
            int t = f->bbs[i].succ[s];
            pdg_bb_t *bt = &f->bbs[t];
            if (bt->pred_n < CBM_PDG_MAX_BB) {
                bt->pred[bt->pred_n++] = i;
            }
        }
    }
}

static void pdg_compute_postdom(pdg_fn_t *f) {
    int n = f->bb_n;
    /* pdom(exit) = {exit}; pdom(x) = all */
    for (int i = 0; i < n; i++) {
        memset(f->bbs[i].pdom, 0, sizeof(f->bbs[i].pdom));
    }
    pdg_bit_set(f, 0, 0);
    for (int i = 1; i < n; i++) {
        for (int j = 0; j < n; j++) {
            pdg_bit_set(f, i, j);
        }
    }
    bool changed = true;
    while (changed) {
        changed = false;
        for (int x = 1; x < n; x++) {
            uint64_t inter[(CBM_PDG_MAX_BB + 63) / 64];
            bool first = true;
            for (int s = 0; s < f->bbs[x].succ_n; s++) {
                int t = f->bbs[x].succ[s];
                if (first) {
                    memcpy(inter, f->bbs[t].pdom, sizeof(inter));
                    first = false;
                } else {
                    for (size_t w = 0; w < sizeof(inter) / sizeof(inter[0]); w++) {
                        inter[w] &= f->bbs[t].pdom[w];
                    }
                }
            }
            if (first) {
                /* leaf: postdom = self only */
                memset(inter, 0, sizeof(inter));
            }
            /* pdom(x) = {x} ∪ inter */
            uint64_t neu[(CBM_PDG_MAX_BB + 63) / 64];
            memcpy(neu, inter, sizeof(neu));
            neu[x / 64] |= (1ULL << (x % 64));
            if (memcmp(neu, f->bbs[x].pdom, sizeof(neu)) != 0) {
                memcpy(f->bbs[x].pdom, neu, sizeof(neu));
                changed = true;
            }
        }
    }
}

/* Emit CDG edges into gbuf (called by the pass after CFG emission). */
static void pdg_emit_cdg(pdg_fn_t *f, cbm_gbuf_t *gb) {
    int n = f->bb_n;
    for (int u = 0; u < n; u++) {
        if (f->bbs[u].succ_n < 2) {
            continue; /* control dependence needs a branch */
        }
        for (int s = 0; s < f->bbs[u].succ_n; s++) {
            int v = f->bbs[u].succ[s];
            uint8_t kind = f->bbs[u].succ_kind[s];
            if (kind == EDGE_SEQ) {
                continue; /* only branch arms carry dependence */
            }
            char sense = (kind == EDGE_FALSE) ? 'F' : 'T';
            for (int w = 0; w < n; w++) {
                if (w == u) {
                    continue;
                }
                /* Ferrante: w is control dependent on edge u→v iff
                 *   w postdominates v  (w ∈ PDOM(v)  → row v, col w)
                 *   and u does NOT postdominate w (u ∉ PDOM(w) → row w, col u) */
                if (!pdg_bit(f, v, w)) {
                    continue;
                }
                if (pdg_bit(f, w, u)) {
                    continue;
                }
                char props[CBM_SZ_128];
                if (f->bbs[w].kind == BB_TERM) {
                    snprintf(props, sizeof(props), "{\"reason\":\"%c\",\"guard\":true}", sense);
                } else {
                    snprintf(props, sizeof(props), "{\"reason\":\"%c\"}", sense);
                }
                cbm_gbuf_insert_edge(gb, f->bbs[u].gbuf_id, f->bbs[w].gbuf_id, "CDG", props);
            }
        }
    }
}

/* ── REACHING_DEF: GEN/KILL solver ─────────────────────────────── */

static void pdg_emit_reaching_defs(pdg_fn_t *f, cbm_gbuf_t *gb) {
    int n = f->bb_n;
    /* union of all set/use vars (sanitized) */
    char *vars[CBM_PDG_MAX_RD_VARS];
    int vars_n = 0;
    for (int i = 0; i < n && vars_n < CBM_PDG_MAX_RD_VARS; i++) {
        pdg_bb_t *b = &f->bbs[i];
        for (int j = 0; j < b->set_vars_n && vars_n < CBM_PDG_MAX_RD_VARS; j++) {
            vars[vars_n++] = b->set_vars[j];
        }
        for (int j = 0; j < b->use_vars_n && vars_n < CBM_PDG_MAX_RD_VARS; j++) {
            vars[vars_n++] = b->use_vars[j];
        }
    }

    for (int vi = 0; vi < vars_n; vi++) {
        const char *v = vars[vi];
        int def_sites[CBM_PDG_MAX_BB];
        int def_n = 0;
        bool used[CBM_PDG_MAX_BB] = {false};
        for (int i = 0; i < n; i++) {
            pdg_bb_t *b = &f->bbs[i];
            for (int j = 0; j < b->set_vars_n; j++) {
                if (strcmp(b->set_vars[j], v) == 0 && def_n < CBM_PDG_MAX_BB) {
                    def_sites[def_n++] = i;
                    break;
                }
            }
            for (int j = 0; j < b->use_vars_n; j++) {
                if (strcmp(b->use_vars[j], v) == 0) {
                    used[i] = true;
                    break;
                }
            }
        }
        if (def_n == 0) {
            continue;
        }

        /* IN/OUT as bitmask over def_sites; worklist iteration.
         * Bit d covers def_sites[d]; the mask is 64 bits wide, so the solver
         * considers the first 64 def sites per variable (bounded, like the
         * other PDG caps). */
        uint64_t gen[CBM_PDG_MAX_BB] = {0};
        uint64_t kill_all = 0;
        for (int d = 0; d < def_n && d < 64; d++) {
            gen[def_sites[d]] |= (1ULL << d);
            kill_all |= (1ULL << d);
        }
        int solver_defs = def_n < 64 ? def_n : 64;
        uint64_t in[CBM_PDG_MAX_BB] = {0};
        uint64_t out[CBM_PDG_MAX_BB] = {0};
        bool changed = true;
        int guard = 0;
        while (changed && guard++ < 64) {
            changed = false;
            for (int i = 0; i < n; i++) {
                uint64_t ni = 0;
                pdg_bb_t *b = &f->bbs[i];
                for (int p = 0; p < b->pred_n; p++) {
                    ni |= out[b->pred[p]];
                }
                /* Only a node that itself defines v kills other defs of v. */
                uint64_t kill_n = (gen[i] != 0) ? kill_all : 0;
                uint64_t no = gen[i] | (ni & ~kill_n);
                if (ni != in[i]) {
                    in[i] = ni;
                    changed = true;
                }
                if (no != out[i]) {
                    out[i] = no;
                    changed = true;
                }
            }
        }

        for (int i = 0; i < n && f->rd_edge_n < CBM_PDG_MAX_RD_EDGES; i++) {
            if (!used[i]) {
                continue;
            }
            for (int d = 0; d < solver_defs; d++) {
                if (in[i] & (1ULL << d)) {
                    char props[CBM_SZ_128];
                    snprintf(props, sizeof(props), "{\"variable\":\"%s\"}", v);
                    cbm_gbuf_insert_edge(gb, f->bbs[def_sites[d]].gbuf_id, f->bbs[i].gbuf_id,
                                         "REACHING_DEF", props);
                    f->rd_edge_n++;
                }
            }
        }
    }
}

/* ── emission (BasicBlock nodes + CFG edges) ───────────────────── */

static void pdg_emit_fn(pdg_fn_t *f, cbm_gbuf_t *gb) {
    for (int i = 0; i < f->bb_n; i++) {
        pdg_bb_t *b = &f->bbs[i];
        char *qn = cbm_arena_sprintf(f->arena, "%s.bb.%d", f->fn_qn, i);
        const char *kind_s = "plain";
        if (b->kind == BB_COND) {
            kind_s = "cond";
        } else if (b->kind == BB_TERM) {
            kind_s = "term";
        } else if (b->kind == BB_EXIT) {
            kind_s = "exit";
        }
        char props[CBM_SZ_256];
        snprintf(props, sizeof(props), "{\"fn\":\"%s\",\"kind\":\"%s\"}", f->fn_qn, kind_s);
        b->gbuf_id = cbm_gbuf_upsert_node(gb, "BasicBlock", b->name ? b->name : "bb",
                                          qn, f->file_path, b->start_line, b->end_line, props);
    }
    for (int i = 0; i < f->bb_n; i++) {
        pdg_bb_t *b = &f->bbs[i];
        for (int s = 0; s < b->succ_n; s++) {
            const char *kind_s = "seq";
            if (b->succ_kind[s] == EDGE_TRUE) {
                kind_s = "cond-true";
            } else if (b->succ_kind[s] == EDGE_FALSE) {
                kind_s = "cond-false";
            } else if (b->succ_kind[s] == EDGE_BACK) {
                kind_s = "loop-back";
            }
            char props[CBM_SZ_64];
            snprintf(props, sizeof(props), "{\"reason\":\"%s\"}", kind_s);
            cbm_gbuf_insert_edge(gb, b->gbuf_id, f->bbs[b->succ[s]].gbuf_id, "CFG", props);
        }
    }
    pdg_emit_cdg(f, gb);
    pdg_emit_reaching_defs(f, gb);
}

/* ── per-function build ────────────────────────────────────────── */

static void pdg_build_function(cbm_gbuf_t *gb, pdg_fn_t *f, TSNode def, const char *fn_name) {
    uint32_t sl = ts_node_start_point(def).row + 1;
    uint32_t el = ts_node_end_point(def).row + 1;
    if (el - sl + 1 > CBM_PDG_MAX_FN_LINES) {
        return;
    }
    TSNode body = pdg_def_body(f, def);
    if (ts_node_is_null(body)) {
        return;
    }
    TSNode *stmts = NULL;
    int n = pdg_collect_stmts(f, body, &stmts);
    if (n == 0) {
        return;
    }
    if (getenv("CBM_PDG_DEBUG")) {
        for (int si = 0; si < n; si++) {
            char *w = pdg_head_word(f, stmts[si]);
            cbm_log_info("pdg.debug.stmt", "fn", fn_name, "type", ts_node_type(stmts[si]),
                         "head", w ? w : "-");
        }
    }
    /* bb 0 = synthetic exit */
    f->bb_n = 0;
    int exit_bb = pdg_new_bb(f);
    f->bbs[exit_bb].kind = BB_EXIT;
    f->bbs[exit_bb].name = "exit";

    pdg_region_t r = pdg_build_region(f, stmts, n, exit_bb);
    if (f->overflow || r.entry < 0) {
        return;
    }
    if (r.tail != exit_bb && f->bbs[r.tail].kind != BB_TERM) {
        pdg_link(f, r.tail, exit_bb, EDGE_SEQ);
    }
    if (getenv("CBM_PDG_DEBUG")) {
        cbm_log_info("pdg.debug", "fn", fn_name, "stmts", pdg_itoa(n), "bbs", pdg_itoa(f->bb_n),
                     "cfg_edges", pdg_itoa(f->cfg_edge_n), "overflow",
                     f->overflow ? "yes" : "no");
    }
    pdg_compute_preds(f);
    pdg_compute_postdom(f);
    if (getenv("CBM_PDG_DEBUG")) {
        FILE *dbg = cbm_fopen("/tmp/pdg_debug.txt", "a");
        if (dbg) {
            fprintf(dbg, "== fn %s ==\n", fn_name);
            for (int i = 0; i < f->bb_n; i++) {
                fprintf(dbg, "bb%d [%s] succ:", i, f->bbs[i].name ? f->bbs[i].name : "?");
                for (int s = 0; s < f->bbs[i].succ_n; s++) {
                    fprintf(dbg, " %d(%d)", f->bbs[i].succ[s], f->bbs[i].succ_kind[s]);
                }
                fprintf(dbg, " pdom:");
                for (int j = 0; j < f->bb_n; j++) {
                    if (pdg_bit(f, i, j)) {
                        fprintf(dbg, " %d", j);
                    }
                }
                fprintf(dbg, "\n");
            }
            fclose(dbg);
        }
    }
    pdg_emit_fn(f, gb);
}

/* ── def discovery: walk the file tree for proc / ad_proc nodes ── */

static void pdg_walk_defs(cbm_gbuf_t *gb, pdg_fn_t *f, TSNode root) {
    TSNode stack[256];
    int top = 0;
    stack[top++] = root;
    while (top > 0 && !f->overflow) {
        TSNode cur = stack[--top];
        const char *t = ts_node_type(cur);
        bool is_def = false;
        if (f->lang == CBM_LANG_PHP) {
            is_def = strcmp(t, "function_definition") == 0 ||
                     strcmp(t, "method_declaration") == 0;
        } else if (f->lang == CBM_LANG_PYTHON) {
            is_def = strcmp(t, "function_definition") == 0;
        } else {
            is_def = strcmp(t, "procedure") == 0;
            if (!is_def && strcmp(t, "command") == 0) {
                char *w = pdg_head_word(f, cur);
                is_def = (w && strcmp(w, "ad_proc") == 0);
            }
        }
        if (is_def) {
            /* name: PHP/Python defs -> name field; Tcl procedure -> name
             * field; Tcl ad_proc -> first non-flag word of the arguments
             * word_list (the command's own name field is the literal
             * "ad_proc"). */
            char *name = NULL;
            if (f->lang == CBM_LANG_PYTHON || f->lang == CBM_LANG_PHP ||
                strcmp(t, "procedure") == 0) {
                TSNode name_node = ts_node_child_by_field_name(cur, TS_FIELD("name"));
                if (!ts_node_is_null(name_node)) {
                    name = pdg_text(f, name_node);
                }
            } else {
                TSNode wl = ts_node_child_by_field_name(cur, TS_FIELD("arguments"));
                if (!ts_node_is_null(wl)) {
                    static const char *flags[] = {"-public", "-private", "-deprecated",
                                                  "-warn", "-debug", NULL};
                    uint32_t wc = ts_node_child_count(wl);
                    for (uint32_t i = 0; i < wc; i++) {
                        TSNode w = ts_node_child(wl, i);
                        if (strcmp(ts_node_type(w), "simple_word") != 0) {
                            continue;
                        }
                        char *txt = pdg_text(f, w);
                        bool is_flag = false;
                        for (const char **fl = flags; *fl; fl++) {
                            if (txt && strcmp(txt, *fl) == 0) {
                                is_flag = true;
                                break;
                            }
                        }
                        if (!is_flag) {
                            name = txt;
                            break;
                        }
                    }
                }
            }
            if (name && name[0]) {
                /* fresh model per function (arena accumulates, arrays reset) */
                pdg_fn_t fn = *f;
                fn.bbs = cbm_arena_alloc(f->arena, sizeof(pdg_bb_t) * CBM_PDG_MAX_BB);
                if (!fn.bbs) {
                    continue;
                }
                memset(fn.bbs, 0, sizeof(pdg_bb_t) * CBM_PDG_MAX_BB);
                fn.bb_n = 0;
                fn.cfg_edge_n = 0;
                fn.rd_edge_n = 0;
                fn.loop_n = 0;
                fn.overflow = false;
                fn.fn_qn = cbm_fqn_compute(f->arena, fn.project, f->file_path, name);
                pdg_build_function(gb, &fn, cur, name);
                /* don't descend into the def: nested procs are their own walk
                 * (rare) — skip to keep bb attribution clean */
                continue;
            }
        }
        uint32_t cc = ts_node_child_count(cur);
        for (uint32_t i = 0; i < cc && top < (int)(sizeof(stack) / sizeof(stack[0])); i++) {
            stack[top++] = ts_node_child(cur, i);
        }
    }
}

/* ── pass entry ────────────────────────────────────────────────── */

static const char *pdg_itoa(int val) {
    static CBM_TLS char bufs[2][32];
    static CBM_TLS int idx = 0;
    char *b = bufs[idx & 1];
    idx++;
    snprintf(b, 32, "%d", val);
    return b;
}

/* Read a file's bytes (best effort). Caller frees via cbm_free. */
static char *pdg_read_file(const char *path, uint32_t *out_len) {
    FILE *fp = cbm_fopen(path, "rb");
    if (!fp) {
        return NULL;
    }
    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    rewind(fp);
    if (size <= 0 || size > (64 * 1024 * 1024)) {
        fclose(fp);
        return NULL;
    }
    char *buf = (char *)cbm_calloc(CBM_MEM_CLASS_EXTRACT, (size_t)size + 1);
    if (!buf) {
        fclose(fp);
        return NULL;
    }
    size_t got = fread(buf, 1, (size_t)size, fp);
    fclose(fp);
    buf[got] = '\0';
    *out_len = (uint32_t)got;
    return buf;
}

int cbm_pipeline_pass_pdg(cbm_pipeline_ctx_t *ctx, const cbm_file_info_t *files,
                          int file_count) {
    if (!cbm_pdg_extraction_enabled()) {
        return 0;
    }
    cbm_log_info("pass.start", "pass", "pdg", "files", pdg_itoa(file_count));
    const char *dbg = getenv("CBM_PDG_DEBUG");
    (void)dbg;

    TSParser *parser = ts_parser_new();
    if (!parser) {
        return 0;
    }
    /* One parser; set_language is cheap and runs once per file. */
    CBMLanguage parser_lang = CBM_LANG_TCL;

    for (int i = 0; i < file_count; i++) {
        CBMLanguage lang = files[i].language;
        if (lang != CBM_LANG_TCL && lang != CBM_LANG_PYTHON && lang != CBM_LANG_PHP) {
            continue; /* other languages are a follow-up */
        }
        if (lang != parser_lang) {
            if (!ts_parser_set_language(parser, cbm_ts_language(lang))) {
                parser_lang = lang;
                continue; /* grammar unavailable — skip silently */
            }
            parser_lang = lang;
        }
        uint32_t source_len = 0;
        char *source = pdg_read_file(files[i].path, &source_len);
        if (!source) {
            continue;
        }
        TSTree *tree = ts_parser_parse_string(parser, NULL, source, source_len);
        if (!tree) {
            cbm_free(CBM_MEM_CLASS_EXTRACT, source);
            continue;
        }
        TSNode root = ts_tree_root_node(tree);
        if (!ts_node_is_null(root)) {
            CBMArena arena;
            cbm_arena_init(&arena);
            pdg_fn_t f;
            memset(&f, 0, sizeof(f));
            f.arena = &arena;
            f.source = source;
            f.file_path = files[i].rel_path;
            f.project = ctx->project_name;
            f.fn_qn = "";
            f.lang = lang;
            pdg_walk_defs(ctx->gbuf, &f, root);
            cbm_arena_destroy(&arena);
        }
        ts_tree_delete(tree);
        cbm_free(CBM_MEM_CLASS_EXTRACT, source);
    }
    ts_parser_delete(parser);
    cbm_log_info("pass.done", "pass", "pdg", "files", pdg_itoa(file_count));
    return 0;
}
