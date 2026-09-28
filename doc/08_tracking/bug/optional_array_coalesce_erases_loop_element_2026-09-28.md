# Optional array coalescing erases the loop element type

Status: release focused HIR/native verification PASS; canonical bootstrap pending.

Windows canonical frozen6b2 Stage2 compiled all 1062 compiler files and passed
independent sanity/receiver checks, but the required full CLI matrix failed
with 2487 compiled files and one failure in `src/app/play/wm_tray.spl`:

```
hir: Unsupported feature: cannot infer field type while lowering wm_tray_dispatch: struct 'ANY' field 'window_id'
```

`wm_daemon_list_windows()` declares `[WindowInfo]?`. Both
`val ws = windows ?? []` and `val ws = wm_daemon_list_windows() ?? []` are valid
source forms. Rust HIR represents the optional declaration as Shared Pointer
to Array(WindowInfo), and `lower_coalesce` retained that wrapper in its result
type. Following for-in inference could not obtain an Array element from a
Pointer, so `w` degraded to ANY. Ambiguous field-layout fallback correctly
refused to guess the `window_id` offset.

The failing verification snapshot used the actual Rust native-build bridge:
`bootstrap_main.run_rt_native_build -> rt_native_build -> NativeProjectBuilder
-> native_project/compiler.rs -> hir::Lowerer`. The diagnostic is emitted by
Rust `hir/lower/expr/access.rs`, not the pure Simple field resolver.

## Correction scope

After the existing BoxInt scalar coalesce handling, narrow only Shared Pointer
whose inner type is Array to that inner Array. Keep the nil check, runtime
unwrap, default branch, and existing scalar boxing rules. Do not allow all
optional pointers to iterate and do not add application type annotations.

A broad Shared Pointer unwrap would change optional bool/float/u64 payload
representations and reference cases outside this defect. Existing optional
integer fixes handle tagged words explicitly; those contracts remain intact.

## Regression evidence

`test/fixtures/native/optional_array_coalesce` contains actual imported types
and an optional-returning function. A decoy struct gives `window_id` a different
index, so a receiver-blind fallback cannot conceal type loss.

- Native project HIR test discovers these declarations with the production
  import map, then checks both coalesced Array<WindowInfo> locals, nominal loop
  bindings, and field slot0 instead of the decoy's slot1.
- LLVM NativeProjectBuilder integration builds that real import closure in
  bootstrap mode without symbol stub fallback. The resulting executable
  checks nil and present results for both source forms and checks all three
  record fields before counting a present row.

The previous optional tuple-array lowering test only required lowering success;
an ANY loop variable could survive tuple destructuring and evade that check.

Canonical bootstrap matrix/Stage3/Stage4 must be verified after landing the fix.
Previously published early Stage2 admission receipts do not make the failed
matrix a PASS.

Release cycle1 at `0f0a2092585c6f9a373b83421e2063d3cb5d0eca` on Linux GNU
with pinned nightly2026-09-27 and LLVM23 passed both tests once
(`--offline --locked --profile bootstrap --features llvm --jobs 9`).
Precise HIR: 1 passed, 0 failed, 0 ignored. Native integration: 1 passed,
0 failed, 0 ignored, with real build/run taking 13.04 seconds. Input manifest
unchanged. Evidence:
`/mnt/simple-bootstrap-6b2/coalesce-release-tests-20260928/release-cycle1`.

The surgical release backport inserts Array-only narrowing before the existing
runtime unwrap. It preserves the older scalar behavior and does not backport
the separate optional BoxInt scalar correction from main.
