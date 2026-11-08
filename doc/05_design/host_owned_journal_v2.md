# Host owned journal propagation

Authored source design, NOT_RUN. This is ownership propagation through existing host capacity and root owners, not a second WAL or a new failure-injection framework.

`HostCapacityOpenV2` has Ready(actual owner), Rejected(error), and CleanupRequired(canonical journal cleanup, error). `host_capacity_owner_open_owned_v2` and `host_capacity_owner_open_quarantined_owned_v2` call canonical owned journal open. Existing projection and recovery code remain authoritative. On projection/recovery error, close the **latest** acquired journal through the canonical owned close turn. Preserve any cleanup-only capability; never fabricate a replayed ledger to hold it. A consumed-error release is rejected with explicit state text, even without a retryable capability. Existing Result entrypoints are unchanged compatibility surfaces; they never call/flatten the new path.

`HostLocalRootOpenV2` mirrors the same variants. Runtime prerequisites occur before journal acquisition; incomplete root cannot return a manufactured local owner. Finite native runtime uses explicit compiled Linux guard before POSIX private-policy loading. Persistent Windows must use its separate native ACL-backed root factory and cannot gain support by a future backend mapping change.

`host_capacity_owner_close_owned_v2` returns the exact canonical `DistributedOperationJournalCleanupTurnV2` including cleanup capability, closed fact, error and release state. Managed finite command uses only typed root/close APIs. `HostLocalCommandReplyV1` carries optional `journal_cleanup` and `cleanup_state`, established before returning a close/open failure. Only Released+closed+emptyerror preserves the original successful reply. Every close error exits2. Canonical cleanup retry retains error reply/output and never upgrades workload success; Unknown stays native-quarantined, ConsumedError has no raw retry, and stale copied tokens cannot delete a replacement lease.

Actual caller migration in the host tree is finite command -> owned root -> owned capacity. Controller app/store/domain and Caret lifecycle owners must carry canonical cleanup through their own turns and retain it before output/report failure. No new public request decoder or authorization bool is introduced. The canonical file-lock generation token is never a raw descriptor.

Executable evidence is authored in `host_owned_journal_spec.spl`; its manual records eight real filesystem/WAL/native-lock scenarios and exact missing platform/close-fault qualification. Global no-build/no-test constraint remains in force.
