# Retained Controller object storage V3

Executable source:
`test/02_integration/lib/orchestration/controller_storage_owned_v3_spec.spl`.
Baseline `870b79c288c416b01a0dc3065177513137cf2215`; source cycle **1/6**.
Status: **NOT_RUN** for Linux execution, Windows execution, runtime, build and
native qualification. These are authored assertions and procedures, not results.

| Authored real Linux scenario | Assertions |
| --- | --- |
| Shared workload replay | Actual retained journal projection preserves its health/lease identity, publishes metadata in the same namespace, closes and reopens it, then replays the workload. |
| All replay domains | Existing source/catalog fixtures flow through desired submission, policy pin, preflight, workload creation and cancellation; reopening preserves each domain and associations. |
| Immutable assignments/packets | Assignment owner IO interoperates with the existing Linux root reader; refreshed proofs do not overwrite the original packet; changed immutable execution is rejected. |
| Relative archive/stale owner | Message retention returns the exact relative digest key; after actual close, the owned call refuses access even while the physical Linux object still exists. |
| Corrupt collision | A real preexisting immutable object with mismatching bytes remains unchanged; publication fails and no metadata operation is admitted. |
| Authority mismatch | A different Controller projection is refused while the original actual journal remains available for canonical close and reopen. |
| Path bounds | A 129-byte segment receives explicit refusal; ordinary digest-addressed records preserve their exact 68-byte leaf. |

The tests acquire real journals through the existing Linux owned opener. They
never fabricate a live lock, journal health ID, Windows token or OS authority.
The dispatch fixture contains real canonical Linux request and signed test-frame
bytes; storing those bytes is not an execution grant or container launch.

Windows qualification procedure — **NOT_RUN**:

1. Acquire the installed protected Controller root through the lead-owned
   authenticated Windows root/config path. Retain the actual native
   WindowsJournalStore opened from that root; no raw DTO/root-string substitute.
2. Use the existing `distributed_operation_journal_open_windows_v3` with the
   Controller authority, retained store and canonical nonce. Retain every
   cleanup-bearing result. Project via `controller_workload_store_project_owned_v3`.
3. Exercise the same desired/policy/preflight/cancellation and workload/assignment
   cases using that journal. Verify the single existing shared WAL namespace,
   original digest record names and replayed operation/assignment relationships.
4. Retain messages, packets and refreshed proofs through owned variants. Pass
   only framed bytes read from the same owner to the lead's actual host route;
   do not interpret returned relative keys or diagnostic roots as native paths.
5. Cause an actual wrong-owner/stale-owner refusal and an immutable collision
   under a test root. Confirm explicit errors, unchanged existing object bytes,
   no second WAL and retained canonical cleanup until release is confirmed.
6. Close/reopen through the real owner and verify persistent replay. Record
   actual Controller identity, store provider, journal scope, host route and
   cleanup receipts. Do not infer successful dispatch from a successful object
   read, pure fixture or role-key DTO.

No Windows native procedure, host status/validate/prepare/execute/inspect route,
deployed credential or end-to-end Controller dispatch is claimed by this lane.
