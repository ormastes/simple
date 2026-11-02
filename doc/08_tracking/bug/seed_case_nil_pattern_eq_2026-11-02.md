# seed_case_nil_pattern_eq_2026-11-02

**Severity:** P0 (stage2_next native-build worker crash, 0xC0000005)
**Status:** fixed in the seed (PR #5882). The source workaround stays in place until phase 3 passes once on the old seed.

## Symptom
A stage2_next (seed-built from release f5b32bda67c) `native-build` of hello dies right after
`phase=load_sources` with `native-build worker terminated with Windows native status 0xC0000005`.
I attached lldb to the worker (`stage2.exe run src/app/cli/native_build_worker.spl ...`). It faults at
`compiler__driver__driver_build__incremental__native_build_cache_scope_key+372`, which is
`movq (%rsi),%rax` with rsi = 0 (nil 3 & ~7).

## Root cause
The Rust seed (`hir/lower/expr/control.rs`) lowered a `case nil:` literal pattern as an
equality. For a `text?` subject this became `rt_string_eq(subject, nil)`, and that returns 0 for nil vs nil.
So the nil arm never matches, the match falls through and yields nil, and
`canon.features` dereferences null. `case None:` takes the dedicated `rt_is_none` path and is correct.

## Fix
- Seed: a nil literal pattern now lowers to `rt_is_none`, at top level and nested (PR #5882). Unit test:
  `test_nil_literal_pattern_on_optional_text_uses_is_none`.
- Source workaround (tagged `@workaround bug=seed_case_nil_pattern_eq_2026-11-02`): `case nil:` was
  changed to `case None:` at the 6 sites in `src/compiler/80.driver/driver_build/`. The remaining sites (1527 sites in 352
  files) are being rewritten by a separate lane.

## Removal
Remove the tags after stage2 is rebuilt with a seed that contains #5882.
