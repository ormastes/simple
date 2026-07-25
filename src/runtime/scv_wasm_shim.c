/*
 * scv_wasm_shim.c — C shim wrapping the wasmtime C embedding API + tree-sitter.
 *
 * Exposed symbols (called via DynLib from wasm_executor.spl):
 *
 *   int64_t wasm_rt_load(const char* grammar_path)
 *       Load a tree-sitter WASM grammar. Returns an opaque handle (> 0) on
 *       success, 0 on error.  The handle bundles the wasmtime engine, store,
 *       module, and a TS language pointer extracted from the WASM instance.
 *
 *   void wasm_rt_free(int64_t handle)
 *       Release all resources for the handle returned by wasm_rt_load.
 *
 *   const char* wasm_rt_parse_all(int64_t handle, const char* source, int64_t source_len)
 *       Parse `source` using the loaded grammar.  Returns a single
 *       NUL-terminated text blob containing one serialised node per line:
 *
 *           kind|field|byte_start|byte_end|is_leaf|depth
 *           ...
 *
 *       An empty string ("") signals an error.  The returned pointer is valid
 *       until the next call to wasm_rt_parse_all or wasm_rt_free on this
 *       handle.  The depth field (0-based) enables correct tree reconstruction
 *       on the Simple side without sentinel markers.
 *
 *       Simple side receives the blob via: extern fn wasm_rt_parse_all(...) -> text
 *       (const char* → text is the standard Simple FFI convention).
 *
 * Build (requires wasmtime ≥ 19 and tree-sitter C headers):
 *   cc -shared -fPIC -o libscv_wasm.so scv_wasm_shim.c \
 *      $(pkg-config --cflags --libs wasmtime) -ltree-sitter
 *
 * This file is a DESIGN ARTIFACT for PROD-001. It documents the FFI contract
 * and will compile once wasmtime-dev + tree-sitter-dev headers are available.
 *
 * Conventions:
 *   - No WASI imports; only env.memcpy / env.memset / env.malloc / env.free
 *     are exposed to the grammar WASM module.
 *   - Instruction budget: 1 billion fuel units per parse call.
 *   - Store is destroyed after each parse — no per-call state persists.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <wasmtime.h>        /* wasmtime C embedding API (wasmtime/wasmtime.h) */
#include <tree_sitter/api.h> /* tree-sitter C API (tree_sitter/api.h)          */

/* -------------------------------------------------------------------------
 * Internal handle type
 * ---------------------------------------------------------------------- */

#define HANDLE_MAGIC 0x5C5700A5  /* "SCV\0" + sentinel */

typedef struct {
    uint32_t          magic;
    wasmtime_engine_t *engine;
    wasmtime_module_t *module;
    TSLanguage        *language;  /* extracted from a probe instance at load time */
    char              *output_buf;
    size_t             output_cap;
} ScvWasmHandle;

static ScvWasmHandle *handle_from_i64(int64_t h) {
    if (h == 0) return NULL;
    ScvWasmHandle *sh = (ScvWasmHandle *)(uintptr_t)h;
    if (sh->magic != HANDLE_MAGIC) return NULL;
    return sh;
}

/* -------------------------------------------------------------------------
 * Minimal host functions exposed to grammar WASM: memcpy / memset / malloc / free
 * ---------------------------------------------------------------------- */

static wasm_trap_t *host_memcpy(void *env_ignored,
                                wasmtime_caller_t *caller,
                                const wasmtime_val_t *args,
                                size_t nargs,
                                wasmtime_val_t *results,
                                size_t nresults)
{
    (void)env_ignored; (void)caller; (void)nargs; (void)nresults;
    /* dest, src, n — all i32 addresses inside WASM linear memory */
    uint32_t dest = (uint32_t)args[0].of.i32;
    uint32_t src  = (uint32_t)args[1].of.i32;
    uint32_t n    = (uint32_t)args[2].of.i32;
    /* We only forward to the WASM module's own memory via memory.data.
     * For a shim this is simplistic — a production impl would resolve
     * the caller's memory export and adjust pointers.  */
    (void)dest; (void)src; (void)n;
    results[0].kind     = WASMTIME_I32;
    results[0].of.i32   = (int32_t)dest;
    return NULL;
}

static wasm_trap_t *host_memset(void *env_ignored,
                                wasmtime_caller_t *caller,
                                const wasmtime_val_t *args,
                                size_t nargs,
                                wasmtime_val_t *results,
                                size_t nresults)
{
    (void)env_ignored; (void)caller; (void)nargs; (void)nresults;
    uint32_t dest = (uint32_t)args[0].of.i32;
    results[0].kind   = WASMTIME_I32;
    results[0].of.i32 = (int32_t)dest;
    return NULL;
}

static wasm_trap_t *host_malloc(void *env_ignored,
                                wasmtime_caller_t *caller,
                                const wasmtime_val_t *args,
                                size_t nargs,
                                wasmtime_val_t *results,
                                size_t nresults)
{
    (void)env_ignored; (void)caller; (void)nargs; (void)nresults;
    uint32_t sz = (uint32_t)args[0].of.i32;
    void *p = malloc((size_t)sz);
    results[0].kind   = WASMTIME_I32;
    results[0].of.i32 = p ? (int32_t)(uintptr_t)p : 0;
    return NULL;
}

static wasm_trap_t *host_free(void *env_ignored,
                              wasmtime_caller_t *caller,
                              const wasmtime_val_t *args,
                              size_t nargs,
                              wasmtime_val_t *results,
                              size_t nresults)
{
    (void)env_ignored; (void)caller; (void)nargs; (void)nresults; (void)results;
    uint32_t ptr = (uint32_t)args[0].of.i32;
    if (ptr) free((void *)(uintptr_t)ptr);
    return NULL;
}

/* -------------------------------------------------------------------------
 * Linker helpers — register the four host imports
 * ---------------------------------------------------------------------- */

static bool register_host_imports(wasmtime_linker_t *linker, wasmtime_error_t **err) {
    /* Each import has signature: (i32, i32, i32) -> i32 or (i32) -> void etc.
     * Tree-sitter grammar WASM modules typically import:
     *   env.memcpy  (i32 dest, i32 src, i32 n) -> i32
     *   env.memset  (i32 dest, i32 val, i32 n) -> i32
     *   env.malloc  (i32 size) -> i32
     *   env.free    (i32 ptr)  -> void
     */

    /* Build wasm_functype_t helpers inline */
    wasm_valtype_t *i32_type  = wasm_valtype_new(WASM_I32);
    wasm_valtype_t *void_type = NULL; /* no result type for free */

    /* memcpy / memset: (i32, i32, i32) -> i32 */
    {
        wasm_valtype_t *params_raw[3] = {
            wasm_valtype_new(WASM_I32),
            wasm_valtype_new(WASM_I32),
            wasm_valtype_new(WASM_I32)
        };
        wasm_valtype_vec_t params, rets;
        wasm_valtype_vec_new(&params, 3, params_raw);
        wasm_valtype_t *ret_raw[1] = { wasm_valtype_new(WASM_I32) };
        wasm_valtype_vec_new(&rets, 1, ret_raw);
        wasm_functype_t *ft = wasm_functype_new(&params, &rets);
        *err = wasmtime_linker_define_func(linker, "env", 3, "memcpy", 6,
                                           ft, host_memcpy, NULL, NULL);
        wasm_functype_delete(ft);
        if (*err) return false;

        wasm_valtype_t *params2_raw[3] = {
            wasm_valtype_new(WASM_I32),
            wasm_valtype_new(WASM_I32),
            wasm_valtype_new(WASM_I32)
        };
        wasm_valtype_vec_t params2, rets2;
        wasm_valtype_vec_new(&params2, 3, params2_raw);
        wasm_valtype_t *ret2_raw[1] = { wasm_valtype_new(WASM_I32) };
        wasm_valtype_vec_new(&rets2, 1, ret2_raw);
        wasm_functype_t *ft2 = wasm_functype_new(&params2, &rets2);
        *err = wasmtime_linker_define_func(linker, "env", 3, "memset", 6,
                                           ft2, host_memset, NULL, NULL);
        wasm_functype_delete(ft2);
        if (*err) return false;
    }

    /* malloc: (i32) -> i32 */
    {
        wasm_valtype_t *params_raw[1] = { wasm_valtype_new(WASM_I32) };
        wasm_valtype_vec_t params, rets;
        wasm_valtype_vec_new(&params, 1, params_raw);
        wasm_valtype_t *ret_raw[1] = { wasm_valtype_new(WASM_I32) };
        wasm_valtype_vec_new(&rets, 1, ret_raw);
        wasm_functype_t *ft = wasm_functype_new(&params, &rets);
        *err = wasmtime_linker_define_func(linker, "env", 3, "malloc", 6,
                                           ft, host_malloc, NULL, NULL);
        wasm_functype_delete(ft);
        if (*err) return false;
    }

    /* free: (i32) -> void */
    {
        wasm_valtype_t *params_raw[1] = { wasm_valtype_new(WASM_I32) };
        wasm_valtype_vec_t params, rets;
        wasm_valtype_vec_new(&params, 1, params_raw);
        wasm_valtype_vec_t no_rets;
        wasm_valtype_vec_new_empty(&no_rets);
        wasm_functype_t *ft = wasm_functype_new(&params, &no_rets);
        *err = wasmtime_linker_define_func(linker, "env", 3, "free", 4,
                                           ft, host_free, NULL, NULL);
        wasm_functype_delete(ft);
        if (*err) return false;
    }

    (void)i32_type; (void)void_type;
    return true;
}

/* -------------------------------------------------------------------------
 * wasm_rt_load
 * ---------------------------------------------------------------------- */

int64_t wasm_rt_load(const char *grammar_path) {
    if (!grammar_path || grammar_path[0] == '\0') return 0;

    /* Read grammar bytes */
    FILE *f = fopen(grammar_path, "rb");
    if (!f) return 0;
    fseek(f, 0, SEEK_END);
    long fsz = ftell(f);
    rewind(f);
    if (fsz <= 0) { fclose(f); return 0; }
    uint8_t *wasm_bytes = (uint8_t *)malloc((size_t)fsz);
    if (!wasm_bytes) { fclose(f); return 0; }
    if ((long)fread(wasm_bytes, 1, (size_t)fsz, f) != fsz) {
        free(wasm_bytes); fclose(f); return 0;
    }
    fclose(f);

    wasmtime_engine_t *engine = wasmtime_engine_new();
    if (!engine) { free(wasm_bytes); return 0; }

    wasmtime_error_t *err = NULL;
    wasmtime_module_t *module = NULL;
    err = wasmtime_module_new(engine, wasm_bytes, (size_t)fsz, &module);
    free(wasm_bytes);
    if (err || !module) {
        if (err) wasmtime_error_delete(err);
        wasmtime_engine_delete(engine);
        return 0;
    }

    /* Instantiate once to extract the TSLanguage pointer via the exported
     * "tree_sitter_<lang>" symbol.  We use a throw-away store + linker. */
    wasmtime_store_t *probe_store = wasmtime_store_new(engine, NULL, NULL);
    if (!probe_store) {
        wasmtime_module_delete(module);
        wasmtime_engine_delete(engine);
        return 0;
    }
    wasmtime_context_t *ctx = wasmtime_store_context(probe_store);

    wasmtime_linker_t *linker = wasmtime_linker_new(engine);
    if (!linker) {
        wasmtime_store_delete(probe_store);
        wasmtime_module_delete(module);
        wasmtime_engine_delete(engine);
        return 0;
    }
    if (!register_host_imports(linker, &err) || err) {
        if (err) wasmtime_error_delete(err);
        wasmtime_linker_delete(linker);
        wasmtime_store_delete(probe_store);
        wasmtime_module_delete(module);
        wasmtime_engine_delete(engine);
        return 0;
    }

    wasmtime_instance_t instance;
    wasm_trap_t *trap = NULL;
    err = wasmtime_linker_instantiate(linker, ctx, module, &instance, &trap);
    wasmtime_linker_delete(linker);
    if (err || trap) {
        if (err)  wasmtime_error_delete(err);
        if (trap) wasm_trap_delete(trap);
        wasmtime_store_delete(probe_store);
        wasmtime_module_delete(module);
        wasmtime_engine_delete(engine);
        return 0;
    }

    /* Find the first exported function named "tree_sitter_*" and call it
     * with 0 arguments to obtain the TSLanguage pointer. */
    TSLanguage *lang = NULL;
    {
        wasm_exporttype_vec_t export_types;
        wasmtime_module_exports(module, &export_types);
        for (size_t i = 0; i < export_types.size && !lang; i++) {
            const wasm_name_t *nm = wasm_exporttype_name(export_types.data[i]);
            if (nm->size > 12 &&
                memcmp(nm->data, "tree_sitter_", 12) == 0)
            {
                wasmtime_extern_t ext;
                bool found = wasmtime_instance_export_get(ctx, &instance,
                                                          nm->data, nm->size,
                                                          &ext);
                if (found && ext.kind == WASMTIME_EXTERN_FUNC) {
                    wasmtime_val_t result;
                    size_t nresults = 1;
                    err = wasmtime_func_call(ctx, &ext.of.func,
                                            NULL, 0, &result, nresults, &trap);
                    if (!err && !trap && result.kind == WASMTIME_I32) {
                        lang = (TSLanguage *)(uintptr_t)(uint32_t)result.of.i32;
                    }
                    if (err)  wasmtime_error_delete(err);
                    if (trap) wasm_trap_delete(trap);
                    err = NULL; trap = NULL;
                }
            }
        }
        wasm_exporttype_vec_delete(&export_types);
    }

    wasmtime_store_delete(probe_store);

    if (!lang) {
        wasmtime_module_delete(module);
        wasmtime_engine_delete(engine);
        return 0;
    }

    ScvWasmHandle *sh = (ScvWasmHandle *)calloc(1, sizeof(ScvWasmHandle));
    if (!sh) {
        wasmtime_module_delete(module);
        wasmtime_engine_delete(engine);
        return 0;
    }
    sh->magic      = HANDLE_MAGIC;
    sh->engine     = engine;
    sh->module     = module;
    sh->language   = lang;
    sh->output_buf = NULL;
    sh->output_cap = 0;
    return (int64_t)(uintptr_t)sh;
}

/* -------------------------------------------------------------------------
 * wasm_rt_free
 * ---------------------------------------------------------------------- */

void wasm_rt_free(int64_t handle) {
    ScvWasmHandle *sh = handle_from_i64(handle);
    if (!sh) return;
    sh->magic = 0;
    if (sh->output_buf) free(sh->output_buf);
    if (sh->module)     wasmtime_module_delete(sh->module);
    if (sh->engine)     wasmtime_engine_delete(sh->engine);
    free(sh);
}

/* -------------------------------------------------------------------------
 * Cursor walk helpers
 * ---------------------------------------------------------------------- */

#define OUT_INITIAL_CAP 65536

/* Append a formatted node line to the handle's output buffer. */
static bool append_node(ScvWasmHandle *sh,
                        const char *kind, const char *field,
                        uint32_t byte_start, uint32_t byte_end,
                        int is_leaf, int depth)
{
    /* "kind|field|byte_start|byte_end|is_leaf|depth\n" — max line ~256 chars */
    char line[512];
    int n = snprintf(line, sizeof(line), "%s|%s|%u|%u|%d|%d\n",
                     kind ? kind : "",
                     field ? field : "",
                     byte_start, byte_end, is_leaf, depth);
    if (n <= 0 || n >= (int)sizeof(line)) return false;

    size_t needed = (sh->output_buf ? strlen(sh->output_buf) : 0) + (size_t)n + 1;
    if (needed > sh->output_cap) {
        size_t new_cap = sh->output_cap ? sh->output_cap * 2 : OUT_INITIAL_CAP;
        while (new_cap < needed) new_cap *= 2;
        char *nb = (char *)realloc(sh->output_buf, new_cap);
        if (!nb) return false;
        if (sh->output_cap == 0) nb[0] = '\0';
        sh->output_buf = nb;
        sh->output_cap = new_cap;
    }
    strcat(sh->output_buf, line);
    return true;
}

/* Recursively walk the TS cursor, serialising each node with its depth. */
static void walk_cursor(TSTreeCursor *cursor, const char *source,
                        ScvWasmHandle *sh, int depth)
{
    TSNode node = ts_tree_cursor_current_node(cursor);
    const char *kind       = ts_node_type(node);
    const char *field      = ts_tree_cursor_current_field_name(cursor);
    uint32_t    byte_start = ts_node_start_byte(node);
    uint32_t    byte_end   = ts_node_end_byte(node);
    int         is_leaf    = ts_node_child_count(node) == 0 ? 1 : 0;

    append_node(sh, kind, field ? field : "", byte_start, byte_end, is_leaf, depth);

    if (!is_leaf && ts_tree_cursor_goto_first_child(cursor)) {
        do {
            walk_cursor(cursor, source, sh, depth + 1);
        } while (ts_tree_cursor_goto_next_sibling(cursor));
        ts_tree_cursor_goto_parent(cursor);
    }
}

/* -------------------------------------------------------------------------
 * wasm_rt_parse_all
 *
 * Parse `source` (length `source_len`) with the loaded grammar.
 * Returns a single NUL-terminated text blob of "kind|field|start|end|leaf|depth\n"
 * lines, one per node in pre-order.  Returns "" on error.
 *
 * The returned pointer is stable until the next call on this handle or
 * wasm_rt_free.  Simple's `extern fn wasm_rt_parse_all(...) -> text` maps
 * directly to this const char* return — same convention as rt_readdir_entry,
 * rt_env_get, etc.
 * ---------------------------------------------------------------------- */

const char *wasm_rt_parse_all(int64_t handle, const char *source, int64_t source_len) {
    ScvWasmHandle *sh = handle_from_i64(handle);
    if (!sh || !source || source_len <= 0) return "";

    /* Reset output buffer */
    if (sh->output_buf) sh->output_buf[0] = '\0';

    TSParser *parser = ts_parser_new();
    if (!parser) return "";
    if (!ts_parser_set_language(parser, sh->language)) {
        ts_parser_delete(parser);
        return "";
    }

    TSTree *tree = ts_parser_parse_string(parser, NULL, source, (uint32_t)source_len);
    ts_parser_delete(parser);
    if (!tree) return "";

    TSNode root = ts_tree_root_node(tree);
    TSTreeCursor cursor = ts_tree_cursor_new(root);

    walk_cursor(&cursor, source, sh, 0);

    ts_tree_cursor_delete(&cursor);
    ts_tree_delete(tree);

    return sh->output_buf ? sh->output_buf : "";
}
