# Linear DCE validator compatibility scenarios

**Authored manual, UNRUN.** No runner or docgen executed. Requirement:
`REQ-C7-DCE-ACTUAL`. Executable:
`test/01_unit/compiler/mir/dce_translation_validation_linear_spec.spl`.

| Scenario | Actual evidence asserted | Status |
|---|---|---|
| Exhaustive bounded differential | 73 programs of length 0–2 from eight instructions, all 5329 source/target pairs; actual validator compared with frozen recursive reference, full retained sequences compared with unchanged abstract optimizer. | UNRUN |
| Redefinitions and dead chains | Read-before-write, repeated destination, nonzero result ID; exact one-pass sequence and separately valid second removal pass. | UNRUN |
| Invalid domain and diagnostics | Negative destinations/result IDs preserve helper behavior, validators reject, missing audit retains precedence over rejection, no certificate on either refusal. | UNRUN |

The bounded enumeration is a regression oracle, not a general equivalence
proof. The source recurrence argument is documented in the design. The frozen
reference comes from immutable d9e177de79ac599ecd4b165e39c26d99f037c357;
external packet records its SHA-256 and initial tests-first snapshots.
