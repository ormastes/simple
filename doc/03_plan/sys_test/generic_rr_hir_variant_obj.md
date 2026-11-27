# System test plan: generic RR + HIR-variant objects

Lane `generic-rr-hir-variant-obj`. Design: `doc/05_design/generic_rr_hir_variant_obj.md`.

## Requirements under test

| Id | Statement |
|---|---|
| REQ-GRR-001 | A generic body edit invalidates exactly the consumers of `generic.body` (the template's own object actions) and no caller. |
| REQ-GRR-002 | A generic signature edit invalidates every consumer with a `generic.signature` edge and nothing else. |
| REQ-GRR-003 | A bound edit invalidates every consumer with a `generic.bound` edge and nothing else. |
| REQ-GRR-004 | A caller (type-arg-bearing) edit invalidates the caller's dependents; the template and sibling callers are not invalidated. |
| REQ-GRR-005 | A `@cfg` variant edit changes the object key and RR producer only for targets that keep the edited arm. |
| REQ-GRR-006 | An unrelated edit yields zero changed facets and an accepted empty plan. |
| REQ-GRR-007 | Two concurrent rebuilds staged from the same prior generation produce identical canonical shard sets; replay is idempotent. |
| REQ-GRR-008 | Corrupt RR shard bytes or a corrupt generic section fail closed: decode rejects and no plan is produced. |
| REQ-GRR-009 | One target-neutral HIR yields one object key per target; keys differ across targets and are stable for equal inputs. |
| NFR-GRR-001 | First object of a unit is emitted within 10 s (`obj_done_ms - hir_start_ms <= 10000`). **Deferred**: a live measurement only — read a real `NativeFileWorkerReceiptV1` from a `SIMPLE_FILE_WORKERS=1` build on the self-hosted binary; no spec asserts it on synthetic receipts (that would be a hardcoded pass). |

## Spec files

| Level | File | Scope |
|---|---|---|
| unit | `test/01_unit/compiler/cache/generic_facet_fingerprint_spec.spl` | facets, fingerprints, changed-facet diff, section codec with bounds/body, corruption |
| unit | `test/01_unit/compiler/cache/generic_rr_exact_invalidation_spec.spl` | `affected_consumers_v1`, `plan_generic_invalidation_v1`: over/under-invalidation controls, rejections |
| unit | `test/01_unit/compiler/driver/hir_variant_object_key_spec.spl` | projection, group winners, malformed cfg, key/partition/producer/sidecar path |
| integration | `test/02_integration/compiler/cache/generic_rr_edit_rebuild_spec.spl` | edit -> changed facets -> RR delta -> staged shards -> plan, for all eight scenarios |
| system | `test/03_system/compiler/feature/generic_rr_hir_variant_obj_spec.spl` | end-to-end over the public owners: two targets, body/signature/bound/caller/cfg/unrelated edits, concurrent staging, corruption |

## Scenario matrix

| Scenario | Unit | Integration | System |
|---|---|---|---|
| body edit | fingerprint diff | plan affected = template object only | x |
| signature edit | fingerprint diff | all callers + template object | x |
| bound edit | bound fingerprint sorted/dedup | all callers + template object | x |
| caller edit | args id changes | caller's consumers only | x |
| cfg-variant edit | projection per target | windows key changes, linux key stable | x |
| unrelated edit | no diff | accepted, empty | x |
| concurrent rebuild | - | equal staged shards, idempotent replay | x |
| cache corruption | section decode fails | shard decode fails, plan rejected | x |

## Known gaps

- REQ-GRR-008's on-disk path (`read_reverse_reference_shard_v1` -> `rr_shard_decode_rejected`
  through the verified CAS) is not exercised: the verified CAS refuses to store
  non-canonical bytes, so a corrupt stored shard needs a filesystem-level fixture. The
  codec-level fail-closed control (`reverse_reference_shard_decode_v1`) and the plan-level
  rejection (`rr_shard_incomplete`) are covered.
- On the Rust seed the positive decode control of the RRS1 envelope fails (`wire_get_u32`
  misreads on the seed; `three_payload_common_v2_contract_spec.spl` is 1/13 there), so one
  `it` in the integration and system specs is seed-RED by construction.

## Evidence rule

Evidence must come from `bin/release/<triple>/simple`. A Rust-seed run is reported as seed
evidence. Until a self-hosted binary exists on this host, every spec is tagged UNRUN in the
plan status row (1A.0) and the manuals under `doc/06_spec` are generated when the binary is
available.
