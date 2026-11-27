# Actual kernel/profile context observation V1

Status: **SOURCE CHECKPOINT / AUTHORED_UNRUN**. No native build, runtime test,
Simple execution or terminal proof is claimed. This distinct source scope follows
`linux_cgroup_terminal_observation_v1.md` and does not reopen the capped provider
primary-association campaign, repair its HOLD, or relax current unknown outcomes.

## Exact boundary

`common/contracts/container/kernel_qualification_v1.spl` defines the frozen six
field profile and strict canonical SDN encode/decode/digest. GNU build IDs are
actual variable-length note bytes, not assumed SHA256 hashes. The sole rule is
`linux-v6.12-core-events-deactivation-v1`. The three source/config/patch hashes
are trusted administrator references; this codec does not attest their contents.

`linux_container_containment_kernel_observe_v1(owner, profile)` returns
`LinuxContainerContainmentKernelTurnV1 {owner, facts?, error}`. Owner retention is
unconditional, including invalid metadata and partial descriptor acquisition.
The native operation extends the existing role-3 registry and shares its origin,
namespace, token/kind and close rules. It creates no second registry or journal.
The public facts have no decoder that could manufacture native authority.

The frozen provider wrapper `LinuxOciInstalledContainmentPolicyV2` contains
`base: LinuxOciInstalledContainmentPolicyV1` and `kernel_profile`. Its canonical
outer version-2 `linux-oci-installed-containment-policy` binds canonical
`basePolicy`/`kernelProfile` strings and both explicit digests. This native lane
does not implement or edit the held provider wrapper/association source. The actual completed Host installation journal pins
those exact wrapper bytes/hash and a separate composite observation identity.
No existing V1 capture becomes qualified retrospectively; this API records
current descriptive facts only. No terminal, eligibility or discharge flag is
introduced, and no provider association success is inferred from it.

## Actual observations

Native code retains at most five additional descriptors per owner: current
captured observer status, root, sysfs root, kernel directory and kernel notes.
Each slot is opened only once and reused, including partial failures; unresolved
FDs are never overwritten or reopened into an accumulating inventory. Close uses
the existing owner-preserving retirement path. Repeated observation is fixed to
the actual thread and pinned observer PID/cgroup/mount namespaces.

It reads the real `/sys/kernel/notes` through no-follow directory/file opens,
checks SYSFS_MAGIC, same native mount/device and exact retained path identities,
and parses at most 65536 bytes / 256 note records. Exactly one GNU build-ID note
of 1..64 bytes is accepted; malformed lengths, duplicate IDs and truncation
refuse. The raw notes hash and actual `uname` release are reported and compared
with the expected installed profile data. This observes the running kernel
notes, not a `/boot` pathname or an external command's output.

The current thread's pinned procfs status is bounded to 65536 bytes and matched
to actual PID/TID. Before and after the bounded notes read, repeated native
`PR_GET_SECCOMP`, `PR_GET_DUMPABLE`, `PR_GET_NO_NEW_PRIVS`, status and namespace
checks require:

- syscall and status seccomp modes both zero;
- TracerPid zero and dumpable zero;
- coherent NoNewPrivs in {0,1}, reported as observed rather than used as a
  substitute for the other protections;
- stable actual thread, proc/sysfs/notes identities and namespaces.

These are point-in-time observations under the existing trusted service/native
code/admin model. They do not provide cryptographic attestation against a hostile
kernel, privileged administrator or arbitrary in-process interposition. This
producer does not set dumpability, install/remove seccomp, enter namespaces,
signal/reap any task, or perform cgroup mutation. A future terminal operation
must reobserve the actual context at its own effect/evidence boundary.

The canonical evidence digest covers every actual fact, installed profile digest
and retained association binding; it excludes the process-local token. Raw source
manifest hashes remain installed references rather than native source proof.

## Pinned source basis

Linux v6.12 commit `adc218676eef25575469234709c2d87185ca223a`:

- [kernel/ksysfs.c, notes](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/ksysfs.c#L236)
  exposes the built-in kernel .notes section as the read-only sysfs notes file;
  blob `1bab21b4718fffd9fa1c76d46827f44af870dd9d`.
- [kernel/sys.c, prctl](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/sys.c#L2480)
  provides the queried process/thread state; blob
  `4da31f28fda81f7dc0fd56fb276133f6bc26e404`.
- [fs/proc/array.c, status](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/proc/array.c#L188)
  reports tracer and thread seccomp/NoNewPrivs facts; blob
  `34a47fb0c57f2570a4f7cb1f45373ddaf2afa883`.

The separate terminal research document preserves removal/deactivation and errno
provenance limitations. This source does not turn ENODEV into a terminal receipt.

## Evidence and blockers

Four pure profile scenarios, one added actual partial-owner refusal scenario,
and a native fixture with independent note vectors / invalid-token calls are
**AUTHORED_UNRUN**. The latter includes the real implementation with symbol
aliases only; it injects no registry entry or successful kernel result. Existing
fork fixture receives only the new export alias for link compatibility and is
not rerun. Native C/Rust ABI twins explicitly refuse unsupported providers.

Positive execution requires an actual managed private PID/cgroup namespace
capture, a protected Host service with dumpable=0 and no unqualified syscall
filter/tracer, an installed profile matching real kernel notes and a completed
Host wrapper-V2 installation. Default dumpability or a filtered execution
container will refuse; the observer does not silently weaken those conditions.
The current held provider association must independently resolve its lifecycle
proof under an authorized scope. No post-query numeric PID comparison is promoted
here into captured-primary continuity.

Still required: actual wrong kernel/build/profile prevention, duplicate/truncated
notes, current-thread/context changes, repeated calls without descriptor growth,
partial syscall/acquisition/close failures, supported positive process context,
installed-policy tampering, Simple text ABI, core/lib/MCP and terminal no-migration/
no-repopulation acceptance. Earlier native observer/fork passes do not qualify
this new code. Historical pointer/host-map failures in unchanged group-owner
sources remain recorded separately; no broad repair or native retry is performed.

## Changed-source static checks

The new ABI received one source-only audit pass of each checker (not a native
campaign):

- `taskset -c 0-4 git diff --check`: exit 0.
- `taskset -c 0-4 sh scripts/audit/direct-env-runtime-guard.shs --working`: exit 0.
- `taskset -c 0-4 python3 scripts/check/check-rt-pointer-ref-map.py`: exit 1;
  the same SRT004 `linux_process_owner.spl:rt_linux_group_collected_stream_v2`
  nil mismatch, 299 edges / one finding, 3969 parameter edges.
- `taskset -c 0-4 python3 scripts/check/check-rt-host-map.py`: exit 1;
  the same 27 FreeBSD/macOS/Windows group-owner gaps recorded in
  `linux_container_containment_source_checks_v1.sdn`, Linux gaps zero.
  Rust provider skips UNKNOWN=1142; compile/link remain UNTESTED.

Neither checker emitted a finding naming the new kernel-observer symbol. This
is not overall verification PASS. No failing group-owner source was modified,
no unchanged audit was retried after these results, and no compile/run followed.
