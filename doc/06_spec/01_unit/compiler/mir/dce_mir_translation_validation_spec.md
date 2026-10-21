# C7 actual MIR DCE observation scenarios

**Authored manual, UNRUN.** No runner or docgen executed. Requirement:
`REQ-C7-DCE-ACTUAL`; design: `doc/05_design/dce_mir_translation_validation.md`.
Executable: `test/01_unit/compiler/mir/dce_mir_translation_validation_spec.spl`.

| Scenario | Actual evidence asserted | Status |
|---|---|---|
| Two dead-chain passes | Real MirBuilder function, actual checked DCE class, 6→5→4 instructions, exact model sequence and distinct before/after hashes, unchanged source. | UNRUN |
| Dispatch boundary | Existing class default and free-function wrapper preserve six instructions; explicit checked class mode removes one. | UNRUN |
| Add boundaries | MAX/MIN/zero/mixed signs and rhs MIN admitted only when safe; signed positive/negative overflow explicitly NotCovered before optimization. | UNRUN |
| Corrupted target | Actual constant/operand/return changes reject; the source return mapping and frozen scalar snapshot remain fixed. | UNRUN |
| Captured snapshot integrity | Stored hash, model instructions with matching target, identity, return anchor and model result-register mutations reject before target validation; untouched captures retain Covered. | UNRUN |
| Candidate isolation | Mutating returned local/signature arrays leaves the caller snapshot unchanged; corrupted candidate rejects. | UNRUN |
| Parameter authority | Both flags, both lists, variadic and Arg-local inconsistencies reject. | UNRUN |
| Malformed SSA | Wrong local type, duplicate declarations, redefinition and undefined reads refuse without updating pass statistics or publishing transformation. | UNRUN |
| Effects/CFG | Checked arithmetic, store, Abort and multiple blocks are explicitly NotCovered. | UNRUN |

Covered is a structural observation, not proof/checker authority. Binary
producer binding, runtime/Lean behavior and performance remain unqualified.
The candidate-rejection return branch is source-reviewed; no injected broken
optimizer is added solely to force that internal branch.

Revision 2 addresses cycle-1 R1/R2. The fixture stores actual LocalIds returned
by MirBuilder; no environment variable forces an assumed allocation layout.
Constant and operand corruptions start from valid covered targets and assert
the exact REFINEMENT diagnostic; repeated assignment uses an actually assigned
destination and asserts the exact SSA diagnostic. Nine actual-MIR scenarios
are authored. Snapshot consistency is not cryptographic authentication.
