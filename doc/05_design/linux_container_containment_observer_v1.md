# Retained Linux container containment observer V1

Status: source checkpoint, **AUTHORED_UNRUN**, observation only. This is a distinct
capability, not a retry of the completed storage/fork/user-mapping campaigns.
The existing registry receives role 3 and retains its process/namespace origin
fence, bounded slots, monotonically issued tokens and per-kind binding checks.
No additional registry, journal, reaper, supervisor or capacity ledger exists.

## Interface and ownership

`std.nogc_sync_mut.io.linux_container_containment_v1` exports capture with PID,
expected canonical cgroup path and association digest; observe takes its opaque
owner; close returns an owner-bearing retirement turn. Snapshot metadata has no
authority decoder. Capture publishes a slot before any native descriptor is
opened, so every partial failure returns that owner. Observe failure retains it.
Close retires descriptors only; any close error permanently retains uncertainty
and never retries a possibly consumed descriptor. Successful retirement conveys
no workload, storage or capacity proof. Windows and Rust twins explicitly refuse.

The provider must independently correlate pre/post exact full CID, scope,
request/profile/baseline pins, primary PID and cgroup, then retain or close the
native owner on association failure. A caller-supplied digest is correlation,
not authentication. Native capture does not require UID mapping or keep-id.

## Native scope

Capture pins pidfd before numeric proc access, verifies live start identity and
exact cgroup path, and checks direct primary membership in bounded cgroup.procs.
It pins actual target PID/cgroup and observer PID/cgroup/mount namespace objects;
target PID and cgroup namespaces must differ from the observer. The first
supported layout has exactly one observer cgroup2 mount rooted at `/`; every
mountpoint/group component is opened no-follow and the group walk must stay on
the selected statx mount. Native mount/device/inode and namespace identities are
retained. Unsupported layouts refuse rather than guess relative namespace roots.

Bounds: 32 shared registry slots, 96 retained descriptors per containment owner,
262144 mountinfo bytes/512 rows, 65536 cgroup.procs bytes and 4096 cgroup.events
bytes. Descriptors from bounded path traversal remain owned until close. Reads
are bounded; no workload command, cgroup write, signal, wait or setns is added.

After capture, observe does not require primary liveness. It rechecks observer
namespace identity, mount identity and pinned directory link/identity around
strict descendant-inclusive events parsing. Missing, removed, stale or unreadable
subjects return no snapshot. `EmptySnapshot` means only that one successful
read observed no live descendants; it **never authorizes discharge**. It cannot
prove lifetime confinement, absence of migration, no-repopulation or successful
child exit. Target namespace descriptors remain pinned after primary death.

Kernel meaning: [cgroup v2 unpopulated notification](https://docs.kernel.org/admin-guide/cgroup-v2.html#un-populated-notification).
A removed cgroup or `ENOENT`/`ENODEV` is unknown, never empty. The final qualified
removal/no-repopulation proof and provider lifetime profile remain unresolved.

## Evidence and required follow-up

No native build/run, compiler check, SSpec/docgen, Windows test or positive
Podman fixture was executed for this checkpoint. New C and Simple fixtures are
authored prevention only. Historical 61/73/163/182 checks are not evidence for
this new kind. The existing fork fixture gets only aliases for the added public
symbols so its source-included owner remains link-compatible; it is not rerun.

Independent Astra source review is required. Positive gates still require exact
private-namespace capture, descendant population after primary death, removal
ordering, namespace/mount drift, alias/reuse refusal, fork/close uncertainty,
provider pre/post association, host same-journal consumption and full core/lib/
MCP qualification. No root capacity guard is removed by this source.

## Source-check result (not verification PASS)

- `taskset -c 0-4 git diff --check`: exit 0.
- `taskset -c 0-4 sh scripts/audit/direct-env-runtime-guard.shs --working`: exit 0.
- `taskset -c 0-4 python3 scripts/check/check-rt-pointer-ref-map.py`: exit 1,
  SRT004 `src/lib/nogc_sync_mut/io/linux_process_owner.spl:rt_linux_group_collected_stream_v2:[i64]`
  nil mismatch. 299 edges, one finding; compile/link UNTESTED.
- `taskset -c 0-4 python3 scripts/check/check-rt-host-map.py`: exit 1,
  27 SRT001 gaps across FreeBSD/macOS/Windows for `rt_linux_group_` symbols:
  `available_capacity_v1`, `cancel_v1`, `collect_v1`, `launch_broker_v1`,
  `parent_acquire_at_v2`, `parent_acquire_v1`, `parent_release_v1`, `poll_v1`,
  `start_v1`. Linux map gaps 0; compile/link UNTESTED, SimpleOS UNKNOWN.

These diagnostics name unchanged group-owner sources, not the new containment
symbols. This is a source-gate **FAIL**, not overall verification PASS; no native
compile/link was attempted and no prior passing test was rerun. Exact base and
unchanged file identities are retained in the adjacent source-check SDN record.
