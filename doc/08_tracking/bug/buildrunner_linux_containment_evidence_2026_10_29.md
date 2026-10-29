# Linux BuildRunner owner: descendant and memory evidence

The earlier live capacity probe launched `/usr/bin/true`. It verified parent
identity, configured limits, and successful cleanup, but did not prove that a
session-changing descendant is retired or that an allocation actually hits the
kernel memory limit. The new native fixtures exercise those two effects through
the production `runtime_linux_group_owner_impl.h` owner.

The descendant forks, calls `setsid`, atomically publishes its PID/session,
and survives its leader. The probe opens a pidfd while it is alive, requires
collection to remain busy, then verifies automatic retirement, SIGKILL, reaping,
and cleanup. The harness uses a subreaper to reap the descendant; the production
owner reaps the leader and observes cgroup retirement. The allocation workload
touches 128 MiB under a 32 MiB cap; the
probe requires exit 137 and a positive kernel `memory.events` `oom_kill` counter,
with neither timeout nor cancellation accounting for that exit.

Both scenarios passed on Linux arm64 in a private OrbStack container cgroup
namespace. This is native C host-component evidence, not proof of Simple ABI
execution or a BuildRunner-managed compile. It tests session escape, not a
privileged workload deliberately modifying cgroup membership or configuration.

- Green log SHA-256: `84382684e5d1eaf940acf5de14c44790294ee22ed246cb5e0c1e1bcf7f7f494e`.
- Negative control: a temporary copy with the memory cap disabled exited 134
  at the required SIGKILL assertion instead of passing. Its failure cleanup
  removed the exact fixture cgroups; the namespace controller state was restored.
- Red log SHA-256: `e0128bce5d7d06c8267208b9970ff1d14a37d93508008d1fe932a44226310874`.
- Logs: `/private/tmp/buildrunner-linux-lane-20261029/containment-{live,no-cap-red}.log`.

`scripts/check/check-linux-capacity-containment.shs` requires already-delegated
memory and never enables host controllers. Missing prerequisites return nonzero,
never PASS. Each run hashes its private scratch path into a distinct cgroup
identity and removes any owned workload on failure. The SSpec wrapper is authored
but unexecuted; it must run through the qualified native Simple test tool before
claiming that layer. Full BuildRunner Hello acceptance remains open.
