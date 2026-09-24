# Driver specs reference removed class fields / option flags (2026-09-15)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Test-wave triage of `test/01_unit/compiler/driver/`: three specs assert fields
that no longer exist on the implementing classes (verified against src on
2026-09-15). Left RED — deleting the assertions would hide the contract change.

1. `mcdc_compile_options_spec.spl` — `CompileOptions.mcdc_dynamic_dormant`
   (read + write + `ctx.config["mcdc_dynamic_dormant"]`). No `mcdc_dynamic*`
   field exists on the options class (`src/compiler/00.common/config.spl`
   carries `mcdc_mode/owner_bytes/global_bytes/include/exclude` only).
2. `storage_projection_registry_spec.spl` —
   `FrozenNativeModuleCapsuleBatchV1.capsule_index`
   (`src/compiler/80.driver/driver_types.spl:115` fields are now
   `ok/registry_identity/capsules/reason`; lookup goes through `find()`).
3. `verified_profile_context_spec.spl` — `CompileContext.assurance_policy_v2`:
   the context carries `assurance_policy: ResolvedAssurancePolicyV1`
   (driver_types.spl:494) while `resolve_assurance_policy_v2` still exists in
   `src/compiler/00.common/assurance/policy.spl` — V2 identity is not retained
   on the context.

Related arity drift: `native_capsule_result_receipt_spec.spl` fails with
`function expects 4 argument(s), but more were provided` — constructor arity
changed.

## Unblock condition

Each is either a deliberate API change (specs must be updated to the new
contract by the owning lane) or a regression (fields must come back). Decide
per item; none are spec-side mechanical fixes.

