# TODO: (simpleorch container) BLOCKED — implement and prove the Linux OCI native-container provider with PODMAN as the default engine; unblock with `apt install podman uidmap` plus lifting `kernel.apparmor_restrict_unprivileged_userns`, or fall back to `usermod -aG docker`

Date: 2026-09-07
Lane: SIMPLEORCH (`.spipe/simple_orchestrator/state.md`)
Owner: whoever holds the SIMPLEORCH lane
Requirement: ORCH-006 (native Linux containers), research §4.2 / §13.5
Status: BLOCKED — missing host privilege, not missing code

## The row

BLOCKED until this host can start an OCI container: implement and prove the
Linux OCI `native-container` provider (create/start/wait/stop/destroy/recover
against a real bundle), then flip the `native-container` receipts in
`test/02_integration/app/ci/pipeline_runner_spec.spl` from BLOCKED to PASS.

## What is missing

An unprivileged OCI container launch is denied on this machine, measured
2026-09-07. Both available paths are shut:

| path | measured result |
|---|---|
| `docker` (present, `/usr/bin/docker`) | `permission denied while trying to connect to the docker API at unix:///var/run/docker.sock` — the user is not in the `docker` group (`id -nG` -> `yoon adm sudo audio dip plugdev users lpadmin`) |
| `podman` | ABSENT — this is now the DEFAULT engine, so installing it is step one |
| `runc --rootless` (present, `runc version 1.3.4`) | `nsexec-1: failed to unshare remaining namespaces: Operation not permitted`, because `/proc/sys/kernel/apparmor_restrict_unprivileged_userns` is `1`. `newuidmap` is absent, so `unshare -Ur` also fails on `/proc/self/uid_map`. |

The probe in `src/app/ci/pipeline_runner.spl` (`probe_container_lane`) tries
podman, then docker, then runc, and reports the binding constraint of the first
candidate it reaches. With podman absent that is docker:

```
docker-daemon-unreachable: permission denied while trying to connect to the
docker API at unix:///var/run/docker.sock
```

With podman installed but the userns restriction in place it reports the
namespace wall instead, which the same probe reproduces by nesting a mount
namespace inside a user namespace — the operation runc.s nsexec performs:

```
userns-nesting-denied: cannot nest a mount namespace in a user namespace;
runc nsexec fails the same way (unshare: cannot change root filesystem
propagation: Permission denied)
```

## Prerequisite — needs privilege this lane must not take

The default engine is now **podman** (rootless), so the preferred unblock is the
rootless one. Chosen by the machine.s owner:

1. **Preferred — rootless podman:** `apt install podman uidmap` AND lift the
   user-namespace restriction (an AppArmor profile granting `userns create`, or
   `sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`). The
   `/etc/subuid` range `yoon:100000:65536` already exists, so `uidmap` plus the
   userns lift is the whole gap. Installing podman ALONE is not enough:
   `newuidmap` is absent and nested namespaces are denied, so rootless podman
   would fail exactly where `runc --rootless` did.
2. **Root fallback — docker:** `sudo usermod -aG docker $USER` (then a new
   login). This gives the lane a root daemon; the probe records
   `privilege: root` so no receipt implies otherwise.
3. Bare `runc` rootless: same prerequisites as (1) minus image management.

No lane may take any of these on its own: they are host-wide privilege changes.
Note that root is NOT inherent to native containers — it is inherent on Windows
(Administrator) and FreeBSD (root), but on Linux rootless is the norm, which is
why podman is the default.

## Exact resume command

The trial bundle is already built and reproduces the failure in one call:

```bash
# bundle: rootfs with the host's STATIC busybox, terminal:false, args echo
runc --root <state-dir> run simpleorch-probe
# expected once unblocked: prints SIMPLEORCH-CONTAINER-OK, exit 0
```

Then, with the lane unblocked:

```bash
bin/simple test test/02_integration/app/ci/pipeline_runner_spec.spl --no-session-daemon
```

and change that spec's third example from asserting `VERDICT_BLOCKED` to
asserting a real container receipt (`VERDICT_PASS`, `attempt == 1`, stdout
containing the run nonce) — the nonce round-trip is the oracle, not the exit
code alone.

## Retained artifacts

- bundle recipe: static `/usr/bin/busybox` copied to `rootfs/bin/busybox`,
  `runc spec --rootless`, `"terminal": false`, args
  `["/bin/busybox","echo","SIMPLEORCH-CONTAINER-OK"]`
- the two error lines quoted above
- `probe_linux_oci()`'s reason string, asserted in the spec so the receipt and
  the probe can never disagree

## What is NOT blocked

The orchestration contracts, the CI pipeline expansion, and the process-lane
runner all execute and are green on this host — see the lane state. This row is
only the container-execution lane. A blocked container job is recorded BLOCKED
and the run verdict is BLOCKED; it is never downgraded to a host process, and
that refusal is itself asserted.

# TODO: (simpleorch container-oci) implement RuntimeProviderV1 create/start/wait/stop/destroy/recover for the Linux OCI lane; blocked on host privilege above, resume command in this file
# TODO: (simpleorch container-evidence) flip the native-container receipts in test/02_integration/app/ci/pipeline_runner_spec.spl from VERDICT_BLOCKED to a real container receipt (attempt 1, run nonce in stdout) once the lane is unblocked

## Engine choice and what "native" costs per host (added 2026-09-07)

The default engine is **podman**, then docker, then bare runc
(`probe_container_lane`). Podman is default because rootless is its normal mode.

Two facts this row must not blur:

- **Podman cannot serve the Windows native lane.** `podman machine` runs a Linux
  guest (WSL2/Hyper-V) and has no Windows-container backend, so it cannot produce
  a process-isolated Windows container. The Windows candidates are
  containerd+runhcs or Docker's Windows-containers backend. The probe refuses
  podman on Windows outright rather than reporting it available.
- **Root is per host, not per container.** Linux rootless needs only user
  namespaces + subuid/subgid + `newuidmap`/`newgidmap` (+ cgroup v2 delegation
  for enforced limits). Windows process isolation requires Administrator and
  FreeBSD jails require root, with no rootless equivalent. `ProbeV1.privilege`
  records which applies, and is `unknown` whenever the lane is unavailable — it
  is never inferred from the engine name.

Source note: HTTPS fetching was unavailable in the session that wrote this
(`HTTPS requires the TLS runtime`), so the two facts above are working knowledge
plus the measured host probes in this file, not re-verified vendor docs.
