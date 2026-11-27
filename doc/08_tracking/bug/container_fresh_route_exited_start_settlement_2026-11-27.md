# Container fresh route: an exited start cannot be settled

- **Status:** FIXED IN SOURCE 2026-11-27 (option 2, decision below). Not live-verified: this host
  has no installed machine policy. The two edge cases left open by that fix (the census refusing on
  lingering engine helpers, and an exit during association) were decided and fixed in source the same
  day; see the last two sections. What is still open is listed at the end.
  Two follow-ups were decided later the same day: the rootless pause process (Edge 3, no source
  change, pinned) and the cleanup error text (Edge 4, fixed in source).
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
- `simple_container_fresh_cleanup_v2` did not settle when this was written. It now attempts the same
  settle; see "Edge 1" below.
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

## Edge 1 (decided and fixed in source 2026-11-27): the census refuses on lingering processes

**Observed on this host** (rootless podman 4.9.3, the developer's own uid, systemd cgroup manager;
not the service-uid route). For `busybox /bin/true`, after `podman start` returned, `conmon`,
`podman container cleanup` and `runc` naming the container id were still alive and were last seen
143 to 169 ms later (three runs). None was seen after `podman rm`. The rootless pause process
(`catatonit`, the user's uid, parent 1, its own `podman-pause-*.scope`) was 27 hours old and stayed.

**Chosen:** repeat the whole settle on a short bound, report a named retryable state at the bound,
and let cleanup drive the same settle.

- `machine_fresh_workload_settle_exited_start_bounded_v3` calls the unchanged
  `machine_fresh_workload_settle_exited_start_v3` at most 8 times inside 2 seconds, sleeping 25, 50,
  100, then 200 ms. Every attempt takes a new full cohort census. The release still needs one
  whole-cohort-empty sample bound to the record; nothing is excluded from the census.
- Only three refusals are repeated, by exact name, decided by the pure reducer
  `machine_fresh_workload_exited_cohort_retry_v3`:
  `fresh-epoch-native-preexisting-service-or-subuid-process`,
  `fresh-epoch-native-uid-census-process-changed` (any host process exiting under the scan) and
  `fresh-population-preexisting-partition-occupant`. Every other refusal returns unchanged at once.
- At the bound the refusal is `machine-fresh-workload-exited-settlement-cohort-retryable:<last census
  reason>`. Nothing is latched and nothing is retained as a diagnostic; `destroy` or cleanup may be
  called again.
- The transfer's `settle_exited_start_v3` now calls the bounded settle, so `destroy` gets it with the
  provider line unchanged. The transfer's `close_v2` (what `simple_container_fresh_cleanup_v2`
  reaches) attempts it before the native close, only when the owner is current, the start is a
  proven exited start, its own Stop, Remove and Absence are completed and the permit is idle
  (`exited_settlement_pending_v3`). Cleanup never runs a helper. If the attempt refuses, the close
  reports that refusal instead of the bare `machine-fresh-workload-charge-retained`.

**Why not exclude the engine's helpers.** The owner retains no kernel identity for conmon, the
cleanup process or a pause process. The only handle is engine text (`.State.ConmonPid`) or a process
name, and neither may weaken the census. A process the owner cannot prove unrelated keeps blocking.

**Why not only a state the caller drives.** The observed linger is well under a second, so a caller
would always need a second call for the common case. The named state is kept for what the bound
does not cover.

**Limit.** A process that never leaves keeps blocking, correctly. If the service-uid route keeps a
rootless pause process the way this host does, every exited-start settle ends in the retryable
state and never settles; the bounded repeat cannot fix that. Not known until a live run.
Answered from source and a host measurement in Edge 3: the service-uid route does not keep one.

## Edge 2 (decided and fixed in source 2026-11-27): the workload exits during association

Two sub-cases, both from source:

1. **First sample `running`, pid gone before capture.** `capture_subject_v2` fails with
   `machine-fresh-workload-native-capture:<reason>`. A containment owner may already be retained.
2. **First sample `running`, subject captured, confirmation says `exited`/`stopped`.** The
   confirmation used to be refused with `machine-fresh-workload-inspect-identity`.

Both returned through `after_association_v2` and latched `outcome_unknown`; `wait`, `logs` and both
settles then refused and the charge stayed retained.

**Chosen:** classify `running` then `exited` as a proven exited start. It is the same two retained
owner samples an exited start already rests on, in the other order a container reaches them.

- Sub-case 1 runs the once-only `inspect-confirm` that path had not reached. Sub-case 2 classifies
  the confirmation it already retains; nothing is run twice.
- The pure reducer `machine_fresh_workload_association_exit_v3` takes the two evidence values, the
  capture refusal and the owner's own observation of its retained subject. It accepts only
  `Running` then `Exited`. A confirmation still `running` keeps the capture refusal; `created` is
  `machine-fresh-workload-start-evidence-changed`; a retained cgroup still populated is
  `machine-fresh-workload-exited-during-association-populated`. Every refusal latches as before.
- A retained subject that no longer answers is no information, not a contradiction: the retained
  descriptors of a dead process and a removed cgroup are expected to stop answering.
- On acceptance the owner closes every descriptor it took (`release_exited_containment_v3`). One
  that does not close refuses and latches. The start is never associated.
- `exited_start_v3` then holds through a second arm that is false for a latched owner and for one
  still holding a descriptor. `start` replies `Exited`, `wait` and `logs` are no longer refused by
  the latch (their own gates are unchanged), and `destroy` reaches the unchanged cohort-census settle. No row and no reducer of the settle changed.

**What the release rests on.** Unchanged: the owner's two retained samples, its own Stop, Remove and
Absence, and custody's whole-cohort-empty sample. The closed descriptors are not evidence that is
given up: custody never bound them, and the census covers every process of the service uid, its
subuid range and the partition.

**Why not a third sample.** The two-sample rule is what an exited start already requires. The launch
projector admits no `--restart` option, so the engine default (no restart) applies and the container
does not leave `exited` by itself. The census is the release ground either way.

## Tested (edges)

`test/01_unit/lib/container/machine_fresh_workload_exit_edges_v3_spec.spl` (8 cases): the retry
reducer (schedule, both bounds, clock failure, every non-census refusal unchanged), the association
reducer (three accepted forms, every named refusal), the held-subject mapping and the shape of the
callers. The lifecycle, effects and transfer changes need installed custody; they were loaded by the
seed but not executed.

## Edge 3 (decided 2026-11-27): the rootless pause process

**Host facts** (podman 4.9.3 rootless, developer uid 1000, subuid 100000:65536, cgroup v2).
- The pause process is `catatonit -P`, real and effective uid 1000 (uid 0 of its own user namespace,
  map `0 1000 1` + `1 100000 65536`), parent 1. It runs as the user's uid, not a subuid.
- Its pid is in `$XDG_RUNTIME_DIR/libpod/tmp/pause.pid` (`/run/user/1000/libpod/tmp/pause.pid`; under
  the route, where `XDG_RUNTIME_DIR` is the run root, `<runRoot>/libpod/tmp/pause.pid`).
- With a user bus, podman moves it into its own `user@1000.service/user.slice/podman-pause-<hex>.scope`.
  That happened even under `env -i`: podman finds `/run/user/<uid>/bus` by uid.
- Without a user bus (emulated with an unusable `DBUS_SESSION_BUS_ADDRESS`), the move fails
  (`Failed to add pause process to systemd sandbox cgroup: dial unix ...`) and the pause process stays
  in the cgroup of the podman command that created it.
- There is no engine setting that runs rootless podman 4.9 without it: `containers.conf(5)` only knows
  the pod infra "pause" image, and `podman --help` has no such option.
- A dead pause process is replaced by the next podman command, which also rewrites `pause.pid`.

**The guest unit.** `simple-orchestrator-host.service` runs as the static `simple-host` user with
`Delegate=yes`; `user@950.service` is masked, and custody refuses an epoch when `/run/user/<uid>/bus`
exists (`epoch_native_no_user_bus_v1`). So the engine can never move the pause process: it stays where
the helper that created it runs.

**Where a helper runs.** Every engine helper is cloned straight into its own group cgroup
(`CLONE_PIDFD | CLONE_INTO_CGROUP`, `src/runtime/runtime_linux_group_owner_impl.h`). When the helper
leader is reaped and the group is still populated, `rt_lg_poll` writes `cgroup.kill`; the group is
collected only once `cgroup.events` says it is empty. The fresh route reaches this through its broker:
the owner's `group_process_stream_poll_v2` is a probe of the broker, the broker's monitor loop
(`native_linux_group_monitor_lease_v1`) calls `linux_process_poll_v1` -> `rt_linux_group_poll_v1`, and a
helper is terminal for the owner only through `broker.tree.sdn`, which the broker writes after
`linux_process_collect_v1`. The exited-start settle refuses while a helper is not retired
(`machine-fresh-workload-exited-settlement-helper-active`).

**Measured** with real podman on this host, each podman command in its own cgroup that was killed after
the command exited, same global flags as the route (`--cgroup-manager=cgroupfs`, private root, run root
and tmpdir, vfs), `--network=none`, no usable bus, `busybox /bin/true`, two runs:
after every one of create, start, inspect, stop, rm and the absence inspect the only process left in the
command's cgroup was `catatonit` (after start also `conmon` and one `podman` process); all were
gone after `cgroup.kill`; every later command made a new pause process and exited 0 (`inspect` said
`stopped`; absence was checked with `podman container exists`, exit 1, not the route's
`container inspect`); at the end no process of the run was left anywhere. A third run with
`INVOCATION_ID` set, which the route's broker environment allows, gave the same result.

**Chosen: no exclusion, no engine setting, no unit change.** The pause process is already placed in a
cgroup that the kernel empties before the census can run: the helper's own group. It is dead before the
settle samples the cohort, so the census has nothing to exclude and the absence proof is unchanged. The
chain is pinned by `test/01_unit/lib/container/machine_fresh_engine_residue_containment_v3_spec.spl`
(4 cases): helper cloned into its group, group killed after the leader is reaped and collected only when
empty, the owner-probe to broker to runtime-poll path, no user bus, cgroupfs manager on every engine
command line, settle only after helper retirement, and exactly one census exemption (the service's own
pid). The pins were green when written; they guard the premises, they are not a fix.

**Why not the others.**
- *A census exclusion keyed on cgroup membership.* The census matches on uid over all of procfs; a cgroup
  rule would excuse every process in that cgroup, which is a class, not a process. That weakens the
  proof for unknown processes.
- *A pidfd the owner holds.* The pause process is a grandchild of a helper, created by the engine. The
  owner can only learn its pid from `pause.pid` (engine text). Taking a pidfd with proof would need a
  dedicated engine no-op in a dedicated cgroup before any workload exists, a retained descriptor per
  epoch and an exemption in both the uid census and the partition population. That is new native
  authority to keep alive a process that the existing containment already removes.
- *A unit setting.* None can help while the census matches on uid, and none is needed.
- *Keeping the pause process alive on purpose.* It would then block the census by design.

**Limit.** This rests on the helper group being killed. The same kill also removed `conmon`
(`container_fresh_route_start_helper_kills_conmon_2026-11-27.md`).

**Changed 2026-11-27 (engine group, built).** The pause process no longer always dies with its helper: when
a `start` helper made it, it is moved with `conmon` into `<delegatedCgroup>/simple-engine-<identity>` and
outlives that one helper. The decision above still holds because the owner kills that group, observes it
empty and removes it **before** the census (`machine_fresh_workload_engine_group_retire_v3`, first line
after the absence check of the exited-start settle). So the census still has nothing to exclude and still
excuses only the service's own pid. The pin gained link 2a (still four cases), and
`machine_fresh_workload_engine_group_v3_spec.spl` pins the order at all three sites.
`pause.pid` can name a dead pid between two helpers; podman replaces it, but a reused pid is a
theoretical hazard that was not observed. The broker is itself a service-uid process; it exits after
publishing its receipt. If the census samples before that, it refuses and the bounded repeat of Edge 1
applies. How long the broker lingers was not measured.

## Edge 4 (decided and fixed in source 2026-11-27): the cleanup error text

`simple_container_fresh_cleanup_v2` wrote the first non-empty stage error onto the retained open value
and returned that text from every later call. So a cleanup that was refused with the retryable state
and then succeeded returned `closed` with the old refusal, and a second, different refusal was hidden
behind the first one.

**Chosen:** a refusal is reported by its own attempt and not kept; a failure is kept.
- A stage that keeps its owner has refused. The same stage runs again on the next call, so its text
  describes that attempt only. It is returned by that attempt and never written to the open value.
- A stage that gave up its owner and still answered with an error, or that neither closed nor kept an
  owner, is a failure nothing will retry. Its text is kept (first one wins) and a cleanup that later
  closes still returns it. The error an open already carried is kept the same way.
- A refused attempt reports its refusal; kept failures stay readable on `retained.error` and are
  returned once the cleanup closes.
- Two answers that used to be silent are named: `container-fresh-cleanup-stage-retained` (owner kept, no
  reason, nothing kept) and `container-fresh-cleanup-stage-unclosed` (not closed, no owner, no reason).

**Why not plain "last attempt wins".** Stage 1 closes with a consumed error, stage 2 refuses; the retry
has no stage 1 left to run and would return clean. That hides a real failure.

**Why not a history field.** Nothing reads one. The refusal is returned to the caller at the time; the
kept failure is the only text that must outlive the attempt.

**Shape.** The pure reducer `container_fresh_cleanup_stage_v2`
(`src/lib/common/contracts/container/fresh_cleanup_stage_v2.spl`), called once per stage by
`simple_container_fresh_cleanup_v2`. No struct changed.

**Below the API (read, not changed).**
- The adapter `close_fresh_v2` and the owner `close_v2` return the transfer's answer per call.
- The transfer `close_v2` returns the settle or native refusal per call without storing it. What it does
  keep, first one wins, is the lifecycle diagnostic (native state error, writer and custody close
  errors); it returns that on every later call and on the final close. Those are failures, and the rule
  above keeps them.
- `machine_fresh_epoch_admission_turn_close_v1` keeps the first error of its own custody owner close
  even when that close only refused. A refused and later successful close of that owner therefore still
  returns the old text from this lower layer. The exited-start retryable state does not pass through it;
  not changed here.
- None of the three stage closes can answer "not closed, no owner": each returns its owner whenever it
  is not closed. `container-fresh-cleanup-stage-unclosed` is a guard for a shape that does not occur
  today.

**Tested.** `test/01_unit/lib/container/fresh_cleanup_stage_v2_spec.spl` (7 cases): refusal then clean,
latest refusal reported, kept failure through a refusal and a success, the open error, the two named
answers, the shape of the API function, and the API function itself on an open value with no owner.
The three stages need installed custody and were not executed.

## Still open

1. **Live guest run.** None of this was run against installed custody.
2. **The pause process in the guest.** Edge 3 says it cannot outlive its helper. That is from source
   and a host emulation, not from a guest run.
3. **What a retained containment descriptor answers after its subject exits.** On this host the
   capture itself is refused (`containment-capture-refused:-95`), so it could not be observed. The
   classification does not depend on the answer unless it is `populated`.
4. **Subject-closure settles are not attempted by cleanup.** Only the exited-start settle is.
5. **The start helper's group kill also killed `conmon`.** Built in source 2026-11-27 (freeze and move
   into an owner-held engine group); not run in the guest. Separate record:
   `container_fresh_route_start_helper_kills_conmon_2026-11-27.md`.
6. **`HOME=/nonexistent`.** Checked 2026-11-27: that value is a rule for the broker's inherited
   environment only. The helpers got an empty environment, so the engine fell back to the account home,
   which custody requires to be the absent `/nonexistent`. Helpers now get `HOME=<run root>`. Record,
   measurements and the open guest unit question: `container_fresh_route_helper_home_2026-11-27.md`.
