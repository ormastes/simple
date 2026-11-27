# Container fresh route: an exited start cannot be settled

- **Status:** OPEN (owner decision needed)
- **Component:** Simple Container shared API, Linux Podman fresh install route
  (`src/lib/nogc_sync_mut/container/machine_fresh_workload_effects_v3.spl`,
  `machine_fresh_workload_settlement_v2.spl`,
  `src/lib/nogc_sync_mut/io/linux_fresh_workload_native_v2.spl`)
- **Found:** 2026-11-27, from source, while making `start` accept a workload
  that already exited. Not observed live: this host has no installed machine
  policy.
- **Spec cases affected:** every `live_run_v1` case of
  `test/03_system/app/container/feature/podman_shared_api_live_spec.spl` whose
  workload exits before the post-Start sample (all the short ones), through the
  after-each cleanup and then `live-prior-cleanup-retained` on later cases.

## Symptom (from source)

`destroy` runs Stop, Remove and Absence, then `settle_v2`. For a start proven
only by exited evidence it now refuses with

```
machine-fresh-workload-exited-start-settlement-unproven
```

Before that name existed the same path refused further down with
`fresh-workload-closure-no-confirmed-subject`. Either way the record stays
unsettled, `close_native_v2` returns `machine-fresh-workload-charge-retained`,
and `simple_container_fresh_cleanup_v2` reports the owner retained.

`podman stop` on an already-exited container exits 0 (observed on this host,
podman 4.9.3 rootless), so Stop does not latch first and the refusal is reached
at settlement.

## Why

Settlement releases the workload's charge only against kernel-side proof:

- `machine_fresh_workload_prepare_settlement_v2` needs `associated` and
  `native_retained` (a captured containment subject).
- `observe_workload_absence_v2` -> `workload_closure_v2` finds the closure by
  matching a subject that association opened from a live pid and cgroup, and
  `machine_fresh_closure_validate_v3` matches it to the captured pid, start
  ticks and cgroup inode.

A workload that exited before the first post-Start sample never had a pid or
cgroup to capture (`.State.Pid` 0, `.State.CgroupPath` empty), so none of that
exists. The only absence evidence is the engine's own "no such container".

## Options (not decided)

1. Allow settlement of an exited start on engine absence alone. This releases
   a charge on engine text, which the reducer forbids today. New authority.
2. Add a kernel-side absence check that needs no captured subject, e.g. custody
   verifying that the deterministic `<delegated cgroup>/libpod-<native id>`
   path does not exist. A new native operation in custody.
3. Make the workload observable before it can exit (hold it at an entry gate
   until association completes). Changes the create projection.

## Acceptance

`destroy` of a workload that exited before association settles, the charge is
released, and `simple_container_fresh_cleanup_v2` returns clean, without a
caller-supplied claim standing in for native evidence.
