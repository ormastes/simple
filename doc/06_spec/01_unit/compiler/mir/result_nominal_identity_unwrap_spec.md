# Result nominal declaration identity

Authored manual; **UNRUN**. No SPipe runner or docgen was executed.

Requirement: `REQ-ENUM-RESULT-NOMINAL-IDENTITY`, a bounded owner-integrity
follow-up to `doc/03_plan/sys_test/robust_any_enum_extension_2026-10-14.md`.
Executable: `test/01_unit/compiler/mir/result_nominal_identity_unwrap_spec.spl`.

| Scenario | Actual API and expected evidence | Status |
|---|---|---|
| Valid nominal owners | Define Struct, Class and Enum in SymbolTable, lower both unwrap paths, retain exact HIR payload and i64 raw copy. Check record owner metadata, requested tag, three existing runtime calls, and mismatch Abort diagnostic. | Authored / UNRUN |
| Wrong declaration ID | Replace the requested table entry with a different real declaration of the same kind. Both unwrap paths, each with fresh and prelowered receiver modes, must produce exactly one fatal diagnostic and no receiver runtime calls, payload type or owner metadata. | Authored / UNRUN |
| Missing/non-type owner | Missing ID and Function declaration remain rejected with the existing exact Named diagnostic. | Authored / UNRUN |
| Erased Any | Both unwrap paths retain the exact fatal Any diagnostic. | Authored / UNRUN |

The fixture calls `MirLowering.lower_result_unwrap_core`; it does not implement
an imitation of the production admission rule. An Error sentinel is supplied in both receiver modes. Fresh-mode refusal
controls for all three declaration kinds and both unwrap paths require exactly
the payload diagnostic; an unexpected evaluation would add
`E-MIR-EXPR-Error`. Prelowered controls remain in place. The
mismatched-ID fixture models malformed/stale HIR metadata, not a demonstrated
well-formed source program failure. No compiler execution or native claim is
made. Existing calls are inspected structurally; allocation and performance
have not been measured.

The source delta adds one ID comparison after the existing symbol lookup.
Valid lowering, generic-argument behavior, defaults, Optional, Result and Dict
carrier rules remain unchanged. The Optional source patch is a separately
reviewed dependency; it is not retested or counted as new completion here.

Revision 2 addresses independent cycle-1 finding R1 (fresh receiver oracle).
Production source is unchanged. All scenarios remain authored / UNRUN.
