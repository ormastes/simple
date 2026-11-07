# Host service domain implementation ownership

Root-authorized implementation worker: existing legacy_container_safety worker,
new isolated worktree/branch. Prior legacy migration worktree and commits remain
unchanged. New workers: N/A; none spawned.

Owned: new `src/lib/nogc_sync_mut/orchestration/host_service_domain_v2.spl` plus
focused new tests/docs. No daemon transport, common schema, provider, journal or
existing host helper edits. Host lead owns renderer extraction 55f77ff3a11 and
canonical owned root/capacity-close propagation. Daemon lead owns generic SDK and
host peer adapter composition. Root/host owns effect split and native process job
integration. Final reviewer and merge owner: root-assigned independent Astra and
root session respectively.

First checkpoint is real immediate metadata handlers, exhaustive readiness/cleanup
propagation and an explicit incomplete effect boundary. All remaining execute,
wait, inspect, cleanup/helper and priority-control paths are required follow-up;
there is no full completion mark or runtime qualification in this checkpoint.
