# Immutable module scalar addresses do not materialize storage

Status: OPEN. Reproduced by a native pure-Simple Phase2 capsule with no stub fallback.

`test/01_unit/compiler/mir/folded_global_scalar_helper_spec.spl` runs actual parser, HIR and MIR lowering. Both address examples fail while the ordinary immutable-read example passes. The final diagnostic variant confirms zero HIR and MIR errors for all inputs:

- Integer `val IMM=7` with two shared addresses, plus mutable `MUT=9` and one mutable address: expected three GlobalAddr instructions and two statics, observed only one GlobalAddr and the mutable static.
- Text/bool immutable scalars with one shared address each: expected two GlobalAddr instructions and two statics, observed zero of each.
- Ordinary immutable read: returns its emitted integer constant and allocates no address storage, PASS.

Evidence: `build/native_probe/traceability-release-folded-spec-pass2/spec-run.log`, `build/native_probe/traceability-release-folded-spec-pass3/spec-run.log`. Process exits zero despite reported failures (separate bug).

Investigate immutable-global recognition/registration and `try_lower_global_addr` admission before materialization. The two corrected calls resolve the module-level type helper but do not by themselves establish address-storage behavior. Do not weaken the test or manufacture backing storage in the test. Three focused attempts are complete; no further retry is authorized in this pass.
