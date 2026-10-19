# G2 effect-aware production correspondence

Executable: `test/01_unit/compiler/mono/model/generic_effect_correspondence_spec.spl`.
Requirement: `REQ-SSPEC-COMPILER`, approved generic formal hardening G2.
Design: `doc/05_design/compiler/generics/generic_effect_correspondence.md`.

**AUTHORED / UNRUN: eight scenarios, zero executed.** This is a hand-maintained
manual, not generated or runtime evidence. Expected outcomes below have not
been observed in this lane. No production refinement proof is claimed.

| Scenario | Actual API and falsifiable oracle |
|---|---|
| commutes for all parameters and a nested thrown function | `substitute_type` result projects to `ms_apply`; original projection unchanged; unchanged generic input rejected |
| rejects the historical behavior that leaves Throws generic | Actual result agrees; explicit stale Throws output disagrees |
| preserves zero arity and distinguishes a missing later parameter | Zero-parameter production result agrees; zero, one and two parameters remain distinct |
| distinguishes effect ordering and custom names from built-in kinds | Reordered effects and Custom("Effect.IO") differ structurally from their controls |
| preserves scalar widths signedness and function return types | i32, i64, u32 and differing returns stay distinct |
| commutes while leaving an unbound variable and literal custom name intact | T substitutes; Outer remains open; Custom("T") remains literal |
| refuses unowned nominal symbols bounds and unresolved HIR | Unsupported source forms return Err and cannot agree with an unknown sentinel |
| refuses unsupported thrown payloads and absent fields instead of erasing them | Unsupported nested payload and absent input/return/parameter/effect fields return Err |

The first scenario uses the steps “Construct the represented production
fragment” and “Compare actual substitution with structural model application”.
The historical counterexample uses “Retain the old output as an explicit
false oracle”. All remaining scenarios directly call the production
projection or substitution APIs with concrete input/output assertions.

The complementary eight scenarios in `generic_effect_substitution_spec.spl`
cover production canonicalization/specialization, ownership, spans, all
effect kinds and absent-versus-empty lists. They are also UNRUN here.
Model proof replay, SSpec runner calibration, compiler/core/MCP smoke and
release admission are not supplied by these manuals.
