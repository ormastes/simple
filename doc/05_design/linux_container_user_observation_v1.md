# Read-only Linux container primary user observation

Status: actual Core-C fixture compiled and ran once, **61 dynamic checks PASS**.
This proves the scoped native observer mechanisms exercised by that fixture.
Simple facade/SSpec, distinct user-namespace mappings, real Podman correlation,
storage executable preparation, and full staged execution remain unqualified.

The module is `std.nogc_sync_mut.io.linux_container_user_observation_v1`.
`linux_container_user_observe_v1(pid, expected_cgroup_path, binding_digest)` returns
an observation or a structured failure with a retained token when cleanup is
unconfirmed. Refresh ignores copied numeric fields and reobserves the original
native baseline. Normal close and failure-close release descriptors only; callers
retain their original owner until close succeeds. Tokens have no wire codec and
are process-local, kind-tagged generations in the existing 32-slot storage
registry, not a second journal or process supervisor.

## Native facts and boundaries

1. Pin `pidfd_open` **before** numeric proc lookup. Pin the proc directory and
   target/caller user namespaces. Require a live pidfd before and after reads.
2. Read bounded status, start ticks, UID/GID maps and cgroup-v2 membership from
   retained proc descriptors. Require primary PID/TGID equality and identical
   consecutive snapshots. Refresh also requires equality with admission facts.
3. Bind the actual observer thread (`/proc/thread-self`), because FSUID/FSGID are
   thread-local. Require its FS credentials equal effective credentials. A
   different calling thread conservatively cannot refresh/consume this token.
4. Require current procfs PID-namespace consistency via the observer NSpid field.
   Require actual namespace descriptor type/identity. A different target user
   namespace is inverse-mapped through nonoverlapping, overflow-checked maps;
   same-namespace IDs are direct, since that uid_map otherwise describes its
   parent's namespace. Read the real configurable overflow UID/GID and refuse
   ambiguous overflow values, including legitimate users with those IDs.
5. Limit each status/map to 64 KiB and each map to 64 ranges. Require a canonical
   non-root cgroup path exactly equal to the configured expected path. Nested
   container cgroups whose provider reports a trimmed parent explicitly refuse.
6. Record actual effective/filesystem UID/GID, uniquely derived container IDs,
   start ticks, userns device/inode identities, map digests, observed wall time,
   expected cgroup and binding digest. Wall time is observation metadata, not a
   freshness grant or execution deadline.

No signal, wait/reap, setns, process adoption, quota change, chmod or workload
launch occurs here. The observer cannot prove that a PID belongs to a particular
container by itself. The canonical Podman owner must independently pre/post-check
the exact full runtime ID, all ownership labels, running state, PID, cgroup and
signed numeric user selection, preserving every returned owner through failure.
The binding digest correlates that trusted provider operation; it is not a
caller-supplied boolean granting execution. Snapshot equality does not seal a
process against later credential, namespace or filesystem changes.

## Storage preparation still required

Root selected an explicit admitted immutable-image keeper followed by separate
exact execution. Existing `/simple-build/inputs` is read-only and
`/simple-build/outputs` writable. Executables are `producer.exe` and `tools/simple`
under inputs. No hidden entrypoint override or arbitrary workload may run before
publication. The native storage consumer must bind retained workspace handles,
the actual target-view file and mount identity, read-only input mounts, absence
of writable aliases/ancestor mounts, exact file digest and single-link ownership.
Two hashes or a copied `readonly=true` value do not establish immutable execution.
Those checks and owner-execute-only preparation are a separate pending source
slice; this observer does not remove the existing workspace execution guard.
Windows selected-user ACL authority remains a separate platform implementation.

## Evidence and limits

The fixture `src/runtime/test/linux_container_user_observation_v1_selfcheck.c`
creates a gated child. It independently compares native facts to real host UID,
GID and namespace identities, exercises wrong binding/cgroup/NUL, kind separation,
cross-thread refusal, generation reuse and FD counts. The child remains alive
after observer close, then the harness releases it and reaps exit 17; the observer
never owns that reap. The one compile/run used CPU affinity 0-4, 2 GiB virtual
memory, bfd, compile timeout 90 s and runtime timeout 20 s. Source/tool/binary
bindings and logs are retained beside the authored manual. No user namespace,
Podman instance, privileged setup or unrelated process was created or controlled.

Remaining mandatory tests include real different-userns mappings, unmapped and
overlapping/oversized maps, credential/namespace changes, actual provider
pre/post races, full Simple lowering and the staged mount/preparation consumer.
Missing facilities remain BLOCKED/NOT_RUN, not passing skips. The SSpec subprocess
case pins the historical compiled artifact hash; a rebuilt artifact requires its
own reviewed manifest/hash before that case is admitted.

## Interface references

- [Kernel procfs descriptor lifetime](https://docs.kernel.org/filesystems/proc.html)
- [Linux pidfd_open semantics](https://man7.org/linux/man-pages/man2/pidfd_open.2.html)
- [Linux user namespace map interpretation](https://man7.org/linux/man-pages/man7/user_namespaces.7.html)
