# Critical enum extension production wiring

Status: **AUTHORED / UNRUN**. This manual was written from the executable spec; docgen was not run.

Executable: `test/01_unit/compiler/mir/critical_enum_extension_wiring_spec.spl`.
Requirement: REQ-002 in `doc/03_plan/sys_test/robust_any_enum_extension_2026-10-14.md`.

Use the existing qualified pure-Simple SSpec runner in an isolated spec process. Each scenario saves the exact nullable safety-profile value, selects the real mode, runs an inline frontend/HIR/MIR pipeline, restores the old value before assertions, and checks actual fatal flags/MIR instructions. No source-string simulation substitutes for lowering.

1. Lower the original and extended ReturnOperand-like enum under critical and mission-critical. The original explicitly covers all variants plus a default; only the newly hidden Borrow variant must produce E-COMPLETE-001.
2. Lower wildcard-only and capture-only matches with `match make():` directly, without a hoisted subject. Require all static variants in the fatal diagnostic, exactly one make call and no runtime enum discriminator/payload calls. Follow the actual probe's unconditional MIR block path and Const/Copy/Move local identities to a return value of 9; reject conditional dispatch, cycles, unknown writes or missing return provenance.
3. Repeat those direct-subject dispatch paths under moderate, strict and robust. Require no fatal finding or trap, exactly one subject call, no enum discriminator/payload calls and the same unconditional default return of 9.
4. Keep an added variant behind an enum default under ordinary profiles. Preserve existing acceptance and no trap.
5. A guarded named arm plus default cannot satisfy critical static coverage; require its variant to remain missing.
6. Same-spelled variants from another owner cannot satisfy the actual subject's coverage. Inspect the full diagnostic collection for exactly one owner mismatch naming Second and First. Assert its existing stored `fatal: false` flag and rejection by the actual `driver_mir_error_is_fatal_v1` legacy classifier; do not confuse the storage flag with downstream authority.
7. A partial no-default critical match keeps its prior diagnostic and one rt_panic/Abort path.
8. A non-enum default remains unaffected by the enum-specific gate.

All eight scenarios are UNRUN. Environment-provider availability, frontend/MIR execution and target/runtime qualification still need evidence. Static source review does not establish runtime or performance success.
