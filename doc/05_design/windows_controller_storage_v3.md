# Controller storage through the retained journal owner V3

Baseline: `870b79c288c416b01a0dc3065177513137cf2215`.
This new routing lane is source cycle **1/6**, with runtime/build/native execution
**NOT_RUN**. It does not reset inherited cycles or repair held SSH/composition,
B1 or active Host lanes. No protected Controller route is implemented here.

The six-file storage closure consists of `workload_store_v1.spl`,
`assignment_objects_v1.spl`, `desired_input_objects_v1.spl`,
`agent_policy_objects_v1.spl`, `agent_preflight_objects_v1.spl` and
`controller_dispatch_objects_v2.spl`, all in
`src/lib/nogc_sync_mut/orchestration/`. Existing Linux root-text public ABIs
remain available with their original signatures. The new owned variants use
the original function stem with `_owned_v3` and receive the actual
`DistributedOperationJournalV2` as their first argument.

Every owned storage entry first validates the current retained owner and
WAL/lease through the existing indexed journal lookup. Windows object IO uses
`distributed_operation_journal_read_required_v3` and
`distributed_operation_journal_publish_v3` through that same native store.
Linux owned variants delegate to the existing root-text implementations after
that owner validation, preserving their publication/readback and explicit
dispatch archive fsync behavior. Workload metadata likewise retains its former
Linux atomic-write path. The platform choice stays in the storage leaf; a stale
or mismatched Windows owner never falls back to root-text IO. No native export,
new journal, secondary index or Windows raw path is added.

| Object domain | Relative address | Existing maximum |
| --- | --- | --- |
| Workload revision | `workload-payloads/<sha256>.sdn` | 8192 bytes |
| Assignment reference/intent/operation | `assignment-objects/<sha256>.sdn` or `.frame` | 4096 / 65536 / 65536 bytes |
| Desired source/manifest | `desired-input-objects/<sha256>.sdn` | 1048576 / 8192 bytes |
| Policy snapshot/catalog | Same desired-input namespace | 1024 / 1048576 bytes |
| Preflight binding/proof | Same desired-input namespace | 65536 / 4194304 bytes |
| Dispatch packet/message | `dispatch-packets/<sha256>.sdn`, `dispatch-messages/<sha256>.sdn` | 2097152 bytes |

The existing relative-path contract permits at most 512 bytes, four components
and 128 ASCII bytes per component. Every route above has two components, a
digest-derived leaf of 68 or 70 bytes and a total of at most 90 bytes. No raw
caller identifier becomes a filename. No existing route was found that cannot
be represented. The owned publishers explicitly reject record-path bounds;
they never truncate a value or change the existing hash scheme. Windows owned
publishers bound byte lengths before publication; preserved Linux wrappers keep
their existing bounds. Immutable content digests remain the existing SHA256 of
the exact encoded bytes.

Windows publication is no-replace followed by bounded owner readback. Linux
keeps its existing guarded publication and readback, including record/directory
flushes in the dispatch archive wrappers; a weaker generic publisher is not
substituted for them. No new power-loss qualification is claimed. Ordinary
object collisions require exact bytes. Dispatch packet collisions keep
the original immutable input comparison: refreshed signatures for the same
assignment/operation/execution may differ, while the first archived packet is
retained. Content-addressed files alone never constitute journal admission.

`controller_workload_store_project_owned_v3(journal, controller_id)` validates
the controller authority and current journal before using the complete existing
projection/recovery implementation. It acquires no new lease. On error, its
caller retains the actual supplied journal for canonical close/cleanup; pending
replay may advance the WAL under that same lease, as in the existing projector.
The lead-owned Windows Controller root must obtain the actual protected store
and open that same shared journal through `distributed_operation_journal_open_windows_v3`.

The internal workload paths migrate on both platforms: workload replay and
publication, desired submit/read/cancel, policy pin/read, preflight retain/read
and assignment retain/read. Existing journal-taking policy/preflight readers
keep their source ABI and replace root-derived reads internally. Desired state,
policy, preflight, cancellation, pending recovery and assignment state machines
are preserved. This storage mechanism adds no caller authentication or grant.

`controller_dispatch_message_retain_owned_v3` returns a **relative archive key**.
It never projects diagnostic `journal.root` into a Windows filename. The lead
consumer must read bytes through that same owner and frame them to its approved
host route. The old root-text V2 message function retains its Linux path result.
Protected root/config/status/host-route integration belongs to the lead lane.

The executable scenarios are in
`test/02_integration/lib/orchestration/controller_storage_owned_v3_spec.spl`.
They use actual Linux journal acquisition, publication, replay and typed close
when executed. Windows procedures are documented in the companion manual and
require a real admitted native store; a fabricated owner is never substituted.
