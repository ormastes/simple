<!-- codex-design -->
# Native module cache invalidation agent task plan

## Shared contracts fixed before implementation

- Types: `NativeModuleCacheWitnessV1`, `NativeModuleCacheDecisionV1`.
- Owners: `native_module_witness_encode_v1`,
  `native_module_witness_read_v1`, `native_module_cache_authorize_v1`, and
  `native_module_shadow_receipt_v1`.
- Manual steps: “Construct the unchanged module witness”, “Apply one semantic
  mutation”, “Re-authenticate the cached object”, and “Inspect the bounded
  shadow decision”.
- Test helpers: `module_action_key`, `dependency_interface`,
  `resolution_digest`, and `oracle_witness_authorizes`.
- Any not-yet-implemented production adapter must `fail(...)`; a no-op or
  unconditional success is forbidden.

## Lanes

| Lane | Scope | Owner |
|---|---|---|
| A | witness schema, canonical codec, fail-closed reader | implementation agent |
| B | semantic dependency/layout/resolution fact collection | implementation agent |
| C | shadow comparison, bounded receipts, promotion gate | implementation agent |
| D | mutation specs and baseline/performance evidence | verification agent |
| Lower-model sidecars | N/A for this bounded design lane; broad implementation may use isolated exploration only after these interfaces are frozen | merge owner decides |

Merge owner: native driver/cache owner. Final reviewer: best available normal or
highest-capability verifier, independent of implementation lanes. Merge order is
A, B, C, D; promotion remains a later separately reviewed change.
