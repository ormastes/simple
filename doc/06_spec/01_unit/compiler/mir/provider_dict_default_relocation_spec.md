# Provider dict-literal default relocation nil key_type guard

Requirement: REQ-SSPEC-COMPILER — regression for
`stage2_test_runner_build_mir_segv_aarch64_2026-10-11` (fixed by PR #2943).
Executable source: test/01_unit/compiler/mir/provider_dict_default_relocation_spec.spl.
Three scenarios, zero placeholders.

| Scenario | Fixture | Expected result |
|---|---|---|
| Nil key_type | `relocate_provider_default(DictLit([], nil, nil))` | no nil dereference; DictLit shape preserved, slots still nil |
| Present key type | `relocate_provider_default(DictLit([], Named, nil))` | key type relocated (non-nil), DictLit shape preserved |
| No error state | nil-key_type relocation on a fresh lowering | zero relocation-family lowering errors |

A provider class field default can transport as a `DictLit` with a nil
key_type (archive/SMF HIR-summary reconstruction leaves the slot absent;
ordinary frontend lowering stamps an `Infer(0, 0)` placeholder instead).
`register_provider_class` -> `relocate_provider_default`'s DictLit arm used
to call `relocate_provider_type(key_type, ...)` unguarded, and the nil
dereference SIGSEGV'd the compiler on the aarch64 stage-2 test_runner build.
The arm now mirrors the pre-existing `value_type` guard; this spec calls
`relocate_provider_default` directly with both slot shapes and pins the
guarded behavior.

Discrimination evidence: forcing the guard off (`if key_type != nil` ->
`if true`) makes both nil-key_type scenarios fail under the seed
interpreter; with the guard in place all three scenarios pass.

Reproduce with the admitted self-hosted runtime once deployed:

```bash
bin/simple test test/01_unit/compiler/mir/provider_dict_default_relocation_spec.spl --mode=interpreter
```

Current-session evidence (Rust seed interpreter, aarch64 Linux host):
`outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0`.
