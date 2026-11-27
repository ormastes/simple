# Container fresh route: an exited start cannot be settled

- **Status:** FIXED IN SOURCE 2026-11-27 (option 2, decision below). Not live-verified: this host
  has no installed machine policy. One related timing case stays OPEN, see the last section.
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

## Symptom (from source, before the fix)

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

## Options

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

## Decision (2026-11-27): option 2, on the custody observation that already exists

**Chosen:** a kernel-side absence check that needs no captured subject. It is not a new native
operation. Custody already has one: `observe_probe_absence_v3`, a census of the whole enforced
cohort (every process of the service uid plus the partition population), and
`machine_fresh_probe_settle_v3` already releases a finite probe's charge on it when the probe
exited before capture. The exited start now settles on that same sample.

**Why not the others.**
- Option 1 releases a charge on engine text. Forbidden, and still forbidden.
- Option 3 changes the create projection (an entry gate inside the container) and every pinned
  created-config check with it, to solve a problem custody can already answer.
- A per-id `libpod-<native id>` path check (the literal form of option 2) would be a new native
  operation and proves less: a missing cgroup directory says nothing about processes that left it.

**What the release rests on.** All three, none caller-supplied:
1. the owner's own two retained post-Start samples proving the exited start (`exited_start_v3`);
2. the owner's own completed Stop, Remove and Absence helpers on its own retained native id;
3. custody's cohort-empty sample, taken after those, bound to this record, epoch and native id
   (assurance, request binding, native id, partition, store, machine, boot, owner generation,
   service process and uid, sample window; one named refusal each).

**The new authority, stated plainly.** One new settlement eligibility: a CPU V2 record may be
released without association when 1 to 3 hold. No new writer, no new native operation, no new
caller input. Engine "no such container" is still only a precondition, never the release ground.

**Limits.**
- The census is cohort-wide, not id-specific. `native_id` in the sample is echoed from the
  owner's own command, not observed. It refuses with
  `fresh-epoch-native-preexisting-service-or-subuid-process` while ANY process of the service
  uid or its subuid range other than the service itself is alive: another workload, a lingering
  conmon or cleanup process, and a rootless pause process if the engine keeps one. The probe
  lane has lived under the same rule; whether a plain CPU workload leaves such a process behind
  is not known until a live run.
- The owner side never latches on that refusal: the settle never calls `unknown_v2`, the charge
  stays retained, and `destroy` may be called again (Stop/Remove/Absence are skipped once done).
  Inside custody, a refused census is a plain `Err`; only a descriptor-close failure moves the
  native slot to `cleanup`, which fails that custody closed. That is the existing behaviour of
  the observation, unchanged here.
- `simple_container_fresh_cleanup_v2` does not settle. If `destroy` was refused, cleanup reports
  the owner retained until a later `destroy` settles.
- `outcome_unknown`, `uncertain`, any held containment, an unretired helper or a non-idle permit
  refuse by name. Workspace and probe records are refused; they keep their own settles.

**Shape.**
- `machine_fresh_workload_exited_settlement_v3.spl` (new): the pure reducer
  `machine_fresh_workload_prepare_exited_settlement_v3`, the binding validator, and the rows. One
  evidence row in its own table `machine-fresh-workload-exited-settlements-v3`, then the unchanged
  V2 release rows.
- `machine_fresh_workload_settle_exited_start_v3` (effects) and `prepare_exited_settlement_v3`
  (lifecycle) are siblings; `settle_exited_start_v3` is the transfer method; the provider's
  `destroy` picks the settle from `exited_start_v3()`.
- `machine_fresh_workload_settle_cpu_v3` is back to its pinned bytes. PR #12218 had added the
  `-exited-start-settlement-unproven` refusal inside it, which broke the body pin in
  `host_linux_service_agent_v4_structure_spec.spl`. That refusal name no longer exists; calling
  the subject settle on an exited start refuses with `machine-fresh-workload-closure-subject-missing`
  or `fresh-workload-closure-no-confirmed-subject` as it did before.

**Tested.** `test/01_unit/lib/container/machine_fresh_workload_exited_settlement_v3_spec.spl`
(5 cases) covers the reducer, every named refusal, the binding validator, the rows and the
dispatch shape. The lifecycle, effects, transfer and provider changes need installed custody and
are unverified beyond loading.

## Still OPEN: the workload exits during association

Not fixed here, on purpose. Two sub-cases, both from source:

1. **First sample `running`, pid gone before capture.** `capture_subject_v2` fails with
   `machine-fresh-workload-native-capture:<reason>`. A containment owner may already be retained.
2. **First sample `running`, subject captured, confirmation says `exited`/`stopped`.**
   `machine_fresh_record_inspect_v3` on the confirmation refuses with
   `machine-fresh-workload-inspect-identity` (status is not `running`). Containment and the
   captured subject are retained; custody never opened a subject for it.

Both return through `after_association_v2`, which latches `outcome_unknown`. Then `wait`/`logs`
refuse, `exited_start_v3` is false (containment held, or the first sample was not `Exited`), the
subject settle has no custody subject, and the exited settle refuses with
`machine-fresh-workload-exited-start-unproven`. The charge stays retained.

Why it is not folded into this fix: the exited settle must not cover `outcome_unknown`, and here
the owner holds a real containment descriptor whose closure was never bound by custody. A fix
needs its own decision, for example a third owner sample plus closing the captured containment
against the same cohort census. The window is the gap between two helper runs, so on the live
spec it is a flake, not a steady failure.
