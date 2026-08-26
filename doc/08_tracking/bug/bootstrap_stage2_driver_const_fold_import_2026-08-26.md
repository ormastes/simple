# Stage 2 driver const-fold import resolves relative to `80.driver`

**Status:** Fixed on isolated branch; protected `main` integration pending in PR #25
**Observed:** 2026-08-26  
**Affected revision:** `67fac9ed179` (also present on fetched `origin/main` at `e35d34f9eeda1b899abd439c56aa8ecec674a1cf`)

## Failure

The sanctioned receipt-free recovery command reached Stage 2 but did not admit
a compiler. The Rust seed compiled
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl` and rejected import
`compiler.semantics.const_fold` with E1034. Resolution incorrectly searched
below `src/compiler/80.driver/compiler`.

Evidence is retained under:

```text
build/bootstrap/release-hardening-stage2/logs/x86_64-unknown-linux-gnu/stage2-native-build.log
build/bootstrap/release-hardening-stage2/stage3/x86_64-unknown-linux-gnu/stage2-command.transcript
```

## Main/release convergence check

A bounded fetch-only check found no corresponding fix on current `origin/main`;
the affected file has no `HEAD..origin/main` diff. Repair must therefore start
as an isolated reviewed `main` fix. If the active release line also contains
the defect, backport that exact reviewed fix through a separate release-targeted
work branch. Do not merge or repoint either protected branch.

## Acceptance criteria

- [x] Remove the accidentally resurrected import/call rather than changing the
  correct resolver or restoring the deleted no-op HIR pass.
- [x] Focused quarantine regression test passes 2/2.
- [x] One receipt-free Stage 2 retry passes the former E1034 boundary.
- [ ] Stage 2 admits a compiler. The retry later failed at link on independent
  unresolved symbols: `aspect_module_identity_index`,
  `safetychecker_flag_static_reference`, `mir_type_probe_text`,
  `MirToLlvm.emit_panic_trap_ir`, and `interp_enum_discriminant_raw`.
- [ ] PR #25 lands on protected `main` through integration authority and is
  backported only when the release-line comparison proves it is required.
