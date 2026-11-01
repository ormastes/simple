# Frozen stage2 reports garbage HirType carriers for two struct fields during phase-3 MIR

- **ID:** stage2_mir_field_type_garbage_carrier_2026-11-01
- **Priority:** P2 (warning only today; P1 if stage3 smoke shows the fields miscompiled)
- **Status:** open
- **Owner area:** `src/compiler/50.mir` MirLowering transient-scope ownership (unassigned; same family as `mir_transient_scope_unpromoted_rti_av_2026-11-01.md`, fixed in source by #5753)
- **Found by:** phase-3 runs 13/14c, frozen stage2 `C:/dev/p3new/stage2.exe` (source ef0681fc0e1), release tip 5fad50cca24

## Symptom

```
[mir-field-type] struct=BackendError field=span actual=2589120870
[mir-field-type] struct=CompiledUnit field=entry_point actual=2589120870
```

`actual` is not a valid HirType kind tag. It reads like a freed or reused carrier
slot, which is the same signature #5753 fixed for rti/rti_last_error/extern ABIs/
erased-callback bindings.

## Why it persists after #5753

The lines are printed by the frozen stage2 while it lowers the current source. #5753
fixes `promote_transient_owner` in the source, so the fix only takes effect in a
compiler built from that source (stage3). Stage2 itself keeps the bug. The open
question is whether some other MirLowering-owned table still escapes
`promote_transient_owner` at HEAD.

## Risk

If codegen lays out `BackendError.span` or `CompiledUnit.entry_point` with the wrong
type, the stage3 binary will misbehave on backend error reporting and entry-point
selection.

## Checks

1. Stage3 smoke (`scripts/bootstrap/p3-smoke-stage3.shs`) must exercise entry-point
   selection (hello compile+run) and one backend error path.
2. Self-build with stage3. If these lines disappear, the stage2-only explanation is
   confirmed. If they remain, audit the MirLowering tables not covered by #5753.

## Removal condition

Close when a stage3 self-build prints no `[mir-field-type] ... actual=<non-kind>` lines.
