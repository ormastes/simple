# Immutable module scalar addresses do not materialize storage

Status: FIXED IN REVIEW BRANCH; protected integration pending. Reproduced by a native pure-Simple Phase2 capsule with no stub fallback.

`test/01_unit/compiler/mir/folded_global_scalar_helper_spec.spl` runs actual parser, HIR and MIR lowering. Both address examples fail while the ordinary immutable-read example passes. The final diagnostic variant confirms zero HIR and MIR errors for all inputs:

- Integer `val IMM=7` with two shared addresses, plus mutable `MUT=9` and one mutable address: expected three GlobalAddr instructions and two statics, observed only one GlobalAddr and the mutable static.
- Text/bool immutable scalars with one shared address each: expected two GlobalAddr instructions and two statics, observed zero of each.
- Ordinary immutable read: returns its emitted integer constant and allocates no address storage, PASS.

Evidence: `build/native_probe/traceability-release-folded-spec-pass2/spec-run.log`, `build/native_probe/traceability-release-folded-spec-pass3/spec-run.log`. Process exits zero despite reported failures (separate bug).

Investigate immutable-global recognition/registration and `try_lower_global_addr` admission before materialization. The two corrected calls resolve the module-level type helper but do not by themselves establish address-storage behavior. Do not weaken the test or manufacture backing storage in the test. Three focused attempts are complete; no further retry is authorized in this pass.

## 2026-10-11 resumed repair

The user requested syncing and landing the fixes on release. Against release snapshot `8303221132a0e44a739b30f92c3a1b7723534e86`, successful `lower_const` now populates `global_constants_by_id` with the same resolved-symbol constant stored in the module. Previously that cache had readers and resets but no population; immutable address materialization therefore returned nil.

Final native pure-Simple capsule: **3 examples, 0 failures**. It verifies repeated integer immutable addresses, mutable address precedence, text/bool initialized canonical storage, and an ordinary immutable return without address storage. Text enum assertions match required variants and compare exact payloads because native boxed-text enum equality is independently defective. Evidence: `build/native_probe/traceability-release-sync-20261011-pass3/regression-receipt.json` and `spec-run.log`. Astra high-effort source review found zero P0/P1; this is local review, not authenticated admission.
