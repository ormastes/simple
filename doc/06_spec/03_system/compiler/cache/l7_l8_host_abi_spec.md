<!-- codex-system-test; manual mirror of the executable P08 sidecar -->
# P08 writer/journal/selected-head recovery [importance=critical; importance_weight=3]

**Executable suite:** `test/03_system/compiler/cache/l7_l8_host_abi_spec.spl`
**Fixture adapter:** `test/03_system/compiler/cache/fixtures/l7_l8_host_abi_v3.spl`
**Evidence class:** physical descriptor-bound writer/recovery evidence.

## Status

The seven rows below are structurally present and remain `MissingEvidence`.
The reconciliation base has the frozen V3 ABI declarations, but this lane has
no qualified issuer-bound provider that can hold the existing journal,
selected-head, writer epoch, reader pin, and recovery scope across processes.
The adapters fail before mutation; copied DTOs, model journals, static scans,
and Rust-seed results cannot supply publication authority or acceptance credit.

## Frozen P08 rows

| Scenario | Exact manual step | Requirement mapping | Required owner evidence |
|---|---|---|---|
| HABI-01 | `Sync the same opened immutable descriptor and its parent directory` | REQ-CSM-007, REQ-CSM-008 | Descriptor identity, actual sync, and parent-directory receipt |
| HABI-02 | `Distinguish selected-head replacement from directory durability` | REQ-CSM-007, REQ-CSM-008 | Post-rename fsync fault is `Unknown`; no old-head assertion |
| HABI-04 | `Compare the expected old head separately from the target head` | REQ-CSM-008 | Old/target transition receipt and copied-target rejection |
| HABI-05 | `Report a competing head without attributing its publication to this attempt` | REQ-CSM-009 | Competing writer receipt; this operation remains absent |
| HABI-06 | `Recover the exact committed operation after cancellation or lost acknowledgement` | REQ-CSM-007, REQ-CSM-008, REQ-CSM-009 | Same writer, operation, generation, and manifest resolve without replay append |
| HABI-07 | `Keep pruned or ambiguous durable history outcomes unknown` | REQ-CSM-007, REQ-CSM-008 | Torn, pruned, missing, and divergent history remain `Unknown` |
| HABI-09 | `Preserve scope ownership across failed finish abort and handle reuse` | REQ-CSM-009, REQ-CSM-012 | Retained recovery scope and complete root protection prevent foreign release/deletion |

The fixture names are frozen: `setup_l7_l8_host_namespace_fixture_v3`,
`open_l7_l8_descriptor_fixture_v3`, `inject_l7_l8_host_fault_v3`,
`run_l7_l8_guarded_publish_v3`, `capture_l7_l8_durable_recovery_v3`,
`check_l7_l8_exact_operation_v3`, `check_l7_l8_current_head_v3`,
`check_l7_l8_descriptor_binding_v3`, `collect_l7_l8_complete_root_union_v3`,
`check_l7_l8_protected_candidate_v3`, `check_l7_l8_scope_cleanup_v3`, and
`check_l7_l8_authority_refusal_v3`. They must be replaced by calls to the
qualified owner, not reimplemented in SSpec.

## Execution gate

Run once after the provider is admitted:

```text
bin/simple test test/03_system/compiler/cache/l7_l8_host_abi_spec.spl --native
bin/simple spipe-docgen test/03_system/compiler/cache/l7_l8_host_abi_spec.spl --output doc/06_spec --no-index
```

No runtime, docgen, power-loss, or production-admission result is claimed by
this structural sidecar. The existing journal/CAS/GC and selected-head owners
remain authoritative, and a failed or indeterminate finish retains recovery
protection rather than publishing a stale or mixed root.
