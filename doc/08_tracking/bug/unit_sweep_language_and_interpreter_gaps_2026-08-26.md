# Language / interpreter gaps surfaced by the full `test/01_unit` sweep (2026-08-26)

Found by the 5-agent sweep-fix campaign (`.spipe/simply_showcase/state.md`).
These are NOT spec/library typos — each needs a compiler or runtime change.
Mechanical failures were fixed and landed (`dddd834f996`, `c433e5d091d`,
`6e7b2eb616a`, `9c5595b146d`, `4907ce1da97`, `e5a10e3ee78`, `f65ae4a5f9c`,
`d9ca9d78b1d`, `2f3f215003b`).

## Grammar / parser

1. **Inline `if c: a else: b` expression** — "expected expression, found Else".
   Blocks `src/lib/common/crypto/x25519_mlkem768/matrix_receipt.spl:148` (5
   specs) and the multi-line `if … else if … else:` expressions in
   `src/lib/hardware/rv64gc_rtl/imac_protected_core.spl:296,529` (2 specs).
2. **`_1` placeholder inside a call argument** lifts the whole enclosing
   `expect(...)` argument into a lambda (worked around in
   `test/01_unit/std/common/text_helpers_spec.spl`).
3. **Typed empty-array constructor `[(i64,i64,i64,i64)]()`** fails at runtime
   with "variable `i64` not found" (worked around in `skia/resample_spec`).
4. **Unterminated f-string** on a 30-line embedded shell string
   (`hardware/debug/testbench_self_referential_generic_class_spec.spl`).

## Interpreter (Rust seed)

5. **Block-scoped `val` leaks out of the declaring `if` block only sometimes** —
   `idx3` declared in one `if` and read in the next: "variable not found".
   Fixed at call sites in `jwt/encode.spl`, `os/crypto/jwt.spl`; the same
   shape still fails in `browser_renderer_protocol_spec` and
   `wasm_host_spec` (match-arm binding `module_id`).
6. **`BTreeMap.new()` / `HashMap.new()` intercepted as builtin Dict before
   user-class lookup** (`interpreter_call/mod.rs:684`,
   `interpreter_method/mod.rs:1824`) — breaks both `src_collections_facade`
   specs; unfixable from `.spl`.
7. **`type X = SharedX` drops static constructors** (`X.new_persistent()` →
   nil); worked around with `export use …{SharedX as X}` in
   `db/dbfs_engine/{intent_log,checkpoint_ring}.spl`. Same class: a constructor
   annotated `-> Ref?` makes later `r.set()` mutations lost
   (`nogc_async_immut/ref/__init__.spl:150`).
8. **"cannot index assign value of type array"** — `sha512_verify`,
   `font_asset_manifest`, `simple_web_file_renderer`, `xz_lzma2`.
9. **Cross-module class-name collision** (`Rect` no field `x` when two modules
   define `Rect`) — `wine_x11_adapter`, `wine_gui_hello`.
10. **Flattened-unit name collision self-recurses** (`file_rename` stack
    overflow) — both `dbfs_meta_store_facade` specs.
11. **`Any?` return of an enum payload arrives as the enum** — `option_ce`.
12. Legacy `import string` resolves to the `bm_*` dict — both
    `oauth_*_random_int_repro` specs.

## Missing runtime backing (SFFI)

`rt_thread_sleep_ms`, `rt_signal_install`, `rt_check_file_path`,
`rt_ensure_dir`, `rt_font_glyph_index`, `rt_font_load`, `rt_dma_alloc`,
`rt_counterpart_open`; `rt_thread_id` arity mismatch (expects 1 arg).

## Not bugs — spec drift needing a rewrite

`browser_engine/*` DOM model (`.tag/.classes` vs `tag_name/attributes`,
`execute_with_type`), `layout_*` (`layout_inline(doc, ctx)` never existed),
`gc_async_mut/**_facade_spec` (facades never existed; real specs live under
`nogc_async_mut/`), engine 3D/ids API drift, `text/*` Phase-5 modules,
`JsonValue` removal, hardware VHDL/SV content oracles.
