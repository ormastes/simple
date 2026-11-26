# Seed JIT types every extern call by the LAST co-compiled declaration (2026-11-27)

Status: verification-pending (fix landed, not natively verified)

Found while fixing the `FileHandle`/`File` = `AsyncFile` alias collision recorded
under `TODO(seed, P2)` in
`doc/08_tracking/bug/toplevel_for_and_val_underscore_parse_2026-11-26.md`.

## Symptom
1. With the aliases as-is, the seed cannot JIT any module that imports the
   pure-Simple frontend:
   `[jit-fallback] HIR lowering error: Cannot infer field type: struct 'FileHandle' field 'mode' (declared fields: fd)`.
   The whole module runs interpreted (~0.2 s per source line), so
   `robust boundaries --source hir test/01_unit/compiler/lint` exceeds 900 s.
2. Re-exporting the sync classes removes the fallback, and then the JIT-compiled
   frontend crashes with rc=139 on any input, even a 2-line file.

## Root cause of the 139 crash
- Crash site (lldb): `ucrtbase!strlen` <- `rt_text_eq_any`
  (`src/compiler_rust/runtime/src/value/collections.rs`) <- JIT frame
  `HirLowering.lower_type` (`src/compiler/20.hir/hir_lowering/types.spl`,
  `if nm == "":`). JIT frames were mapped with `SIMPLE_JIT_TRACE_ADDR=1`.
- The left operand was `heap_word << 3`: a valid text RuntimeValue boxed again
  as an int (`TAG_INT == 0b000`). `rt_text_eq_any` accepts an aligned word
  `>= 0x10000` as a raw C string, so it called `strlen` on it.
- `nm` comes from `parser_type_kind_named_name` -> `_sffi_tuple_get<text>` ->
  `extern fn rt_tuple_get<T>(tuple: i64, index: i64) -> T?`.
  `src/lib/nogc_sync_mut/sffi/enum_wire.spl` declares the same symbol as
  `extern fn rt_tuple_get(tuple: i64, index: i64) -> i64`.
- The seed flattens co-compiled modules into one HIR unit. Extern return types
  were keyed by bare name (`globals` / `method_return_types`), so the last
  registered declaration typed every call. With `enum_wire` loaded last, the
  frontend's `text` read was typed `i64`, and the `text` result was produced by
  int-boxing the raw word.
- Minimal repro: parse `fn f(x: i64) -> i64:` with `parse_full_frontend`, read
  the param type name with `parser_type_kind_named_name`, compare with `""`.
  Passes alone; rc=139 once `std.nogc_sync_mut.sffi.enum_wire` is imported.
- The alias fix only exposed this. Before it, the module was never JIT-compiled.

## Fix
- Seed: `pipeline/module_loader.rs` `tag_node_function_owners` tags `Node::Extern`
  with its owning module. `hir/lower/module_lowering/module_pass.rs` records
  `(owner, return type)` per extern name in `Lowerer::flatten_extern_owner_returns`.
  `hir/lower/expr/calls.rs` types a direct extern call with the calling module's
  own declaration when declarations disagree (`Lowerer::owner_scoped_extern_return`).
  Rust test: `flattened_extern_return_type_follows_calling_module_declaration`
  (`hir/lower/tests/seed_regression_tests.rs`).
- Simple: `src/lib/nogc_async_mut/io/file.spl` no longer declares
  `type File = AsyncFile` / `type FileHandle = AsyncFile`; `buffer.spl` no
  longer declares `type BufferedReader = AsyncBufferedReader` /
  `type BufferedWriter = AsyncBufferedWriter`. The `std.nogc_async_mut.io`
  facade and the `gc_async_mut` twin re-export the sync classes.
- Specs: `test/01_unit/lib/nogc_async_mut/io/sync_name_alias_no_shadow_spec.spl`,
  `test/01_unit/app/cli/jit_frontend_extern_owner_return_spec.spl`.

## Known gaps
- 194 extern names in `src/**` are declared with more than one return shape. The
  seed fix covers a direct call from a module that declares the extern itself.
  A module that calls an extern it only imports still gets the bare-name type.
- `rt_text_eq_any` (Rust and C twins) still treats any aligned word
  `>= 0x10000` as a raw C string. Raw C strings from externs legitimately reach
  it (`lowering_expr_ops.rs`), and a tagged int cannot be told apart from such a
  pointer. Mis-typed words must be stopped upstream, as this fix does.
- `type Color = EngineColor` (`src/lib/nogc_async_mut/game2d/math/__init__.spl`)
  matches a common class name but is not an async alias; left alone.

## Timing (2026-11-27, Windows, shared box)
`run_robust(["boundaries", "--source", "hir", "test/01_unit/compiler/lint"])`
(142 files, 16,302 lines), measured with PowerShell `PeakWorkingSet64`:

| seed | wall | peak RSS | engine |
|---|---|---|---|
| before: `bound3x-target` seed, aliases as-is | 1514 s | 823 MB | interpreter (`[jit-fallback]`) |
| after: this change's seed | 31.4 s | 2458 MB | JIT, 0 fallbacks |

Output is byte-identical. Peak RSS is 3x higher on the JIT path (JIT code plus
the whole frontend compiled at once). That is recorded here as a perf regression
to follow up, not fixed in this change.

## Follow-up: JIT peak RSS (2026-11-27, branch work/robust-jit-rss-20261127)
Status: verification-pending (fix landed, not natively verified)

The 2458 MB peak is NOT only fixed JIT overhead. Per-file probe
(`rt_process_rss_kib` every 10 files over the 158 `.spl` under
`test/01_unit/compiler/lint`): about 1250 MB floor (JIT code plus the frontend
compiled at once, reached in the first ~25 s) and then roughly 7 MB per file on
top. Parse alone grows ~4.7 MB/file, lowering adds ~2 MB/file. Retention scales
with source size (~500 bytes per source byte); parsing the same file 150 times
grows the same, `ast_reset()` alone does not grow. The interpreter does not
grow (refcount frees per-file data); only the JIT keeps the parser graph, HIR
module and origin table alive.

Fix (`src/app/cli/robust_source.spl`, `_robust_hir_facts`): parse with
`parse_full_frontend_stage4_streaming` (its transient scope reclaims parser
scratch), then run lowering + origin table + fact rows inside a transient array
scope and promote only the fact rows before ending it. Same pattern as
`src/app/compiler_entrypoint/inventory_scratch.spl`. If the scope is
unavailable the file is lowered unscoped.

`run_robust(["boundaries","--source","hir", <dir>])` via a `main` driver on the
seed JIT (PowerShell `PeakWorkingSet64`, Windows, shared box):

| files | before wall / RSS | after wall / RSS |
|---|---|---|
| 1 | 24 s / 1376 MB | 22 s / 1366 MB |
| 8 | 24 s / 1344 MB | 23 s / 1356 MB |
| 32 | 25 s / 1426 MB | 25 s / 1351 MB |
| 158 (whole dir) | 33 s / 2438 MB | 33 s / 1397 MB |

Output of the whole-dir run is byte-identical before and after. Remaining
~1.2-1.4 GB is the fixed JIT floor (the 1-file run costs the same); remaining
per-file growth is ~1-3 MB (the promoted parser module). Bound:
`sh scripts/check/check-robust-hir-rss.shs [simple]` runs
`test/01_unit/app/cli/robust_hir_rss_probe.spl` on the JIT (24 parses of
compiler-sized files): PASS 84 MB with the scopes, FAIL 554 MB without. It is a
probe with `main`, not a spec, because the test runner interprets specs and the
interpreter shows no retention. Specs `bound_origin_facts_spec`,
`robust_source_parity_spec`, `origin_sif_summary_spec` stay green.
