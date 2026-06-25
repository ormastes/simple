# Bug: C export-wrapper emission fails on block-less MirFunction

- **ID:** c_backend_export_wrapper_blockless_fn
- **Found:** 2026-06-25
- **First observed red:** 2026-05-19 (test_result.md: `c_backend_export_spec`, 100% failure rate)
- **Severity:** P2 (existing feature test red; blocks in-process verification of `@export("C")` emission)
- **Category:** Compiler / Backend / C export ABI

## Symptom

`test/01_unit/compiler/backend/c_backend_export_spec.spl` has been failing at a
100% rate since 2026-05-19. Driving `MirToC.translate_module` on a hand-built
exported `MirFunction` with `blocks: []` / `locals: []` (the spec's fixture
shape, via `make_exported_fn`) makes the spec subprocess exit with code 1 — the
assertions (`extern "C" int32_t spl_add_numbers(...)`) never report; the
emission path crashes rather than returning text.

A block-less function built the same way through `MirBuilder` (with
`is_export_c`/`export_name` set post-build) reproduces the crash; the same
function with `is_export_c = false` and the Lua backend's `MirToLua` (which
exercises `MirBuilder`-produced bodies) does NOT crash — so the fault is on the
C export-wrapper emission path (`emit_export_wrappers` /
`emit_function_export_wrapper`, `c_backend_translate_part2.spl` /
`c_backend_translate_part3.spl`), not general MIR→C lowering.

## Impact

- Existing `c_backend_export_spec` is red.
- Lua SFFI (`#LIB-LUA-SFFI-001`) cannot add an in-process
  `@export("C")` → `luaopen_*` `extern "C"` emission assertion until this is
  green. That spec verifies the `.so`/`nm` mechanism via a real `cc` oracle
  instead and documents this gap.

## Repro

```
bin/simple test test/01_unit/compiler/backend/c_backend_export_spec.spl
# -> Passed: 0  Failed: 4  (process exits 1 on the export-wrapper path)
```

## Next step

Localize the crash in `emit_function_export_wrapper` for a function with no
blocks/locals (likely an empty-body / return-type-wrapper assumption). Either
fix the emitter to tolerate body-less exported decls or update the fixture if
the contract legitimately requires a body. Then re-enable the in-process
`luaopen_*` emission assertion in `test/01_unit/lib/lua/lua_native_module_spec.spl`.
