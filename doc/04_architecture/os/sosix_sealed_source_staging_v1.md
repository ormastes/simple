# Authenticated SimpleOS sealed source staging

Status: implemented loader source integration; hosted interpreter diagnostic
evidence only. Compiler-created memory-image launch remains unimplemented.

`executable_image_prepare.spl` now stages the existing authenticated retained
filesystem source through `executable_sealed_source_v1.spl` on runtimes with an
audited mutex implementation. The acquisition reads the existing MountTable
virtual handle as exact binary chunks, checks its admitted digest, copies and
seals bytes in the anonymous-image owner, copies those bytes out, then releases
the temporary image lease before ELF/stack/mapping preparation. It never opens
`canonical_source_path`. DBFS, NVFS and NVFS POSIX use their actual drivers.

This is internal source staging for the existing file admission path. It does
not change the public requested/effective materialization policy and does not
advertise a SOSIX memory execution capability. The loader still authenticates
the retained open binding and issues the existing one-shot authority. Scheduler
adoption, capability attenuation, observation and retained file close/retry
remain with their existing owners. An image label cannot select service grants.

The anonymous registry admits only loader-package operations. References contain
slot and generation; every read/release also checks the retained handle identity
and file generation. These values are lookup coordinates, not permission to
execute. Sealing and returned reads both copy, preventing caller-array mutation
or returned-array mutation from changing retained bytes. A sealed source read
must match both the expected byte length and SHA-256 digest before preparation.

The registry limits retained bytes to 64 MiB and live rows to 256. Both limits
are checked before allocating the retained copy. Exhausted generations are never
reused. Its budget covers retained storage only; input/readback/process-image
copies and mapping pages remain separate allocations bounded by the existing
64 MiB source and mapping-plan limits. Acquisitions release their source lease
after a successful copy or failed read. A lock/unlock failure is a fail-stop
quarantine: retained charges can remain, and later storage operations fail.
Such a failure must not publish a mapped image or report complete cleanup.

The runtime allowlist covers the native pthread/critical-section host providers
and the real atomic slot owner in the current RV64 baremetal runtime. ARM64
`spl_mutex_*` currently returns unconditional success; x86_64 lock/unlock returns
nil. Those runtimes and unknown identities do not install this registry and
keep the existing authenticated owned-file read. The allowlist does not elevate
a successful single-thread lock probe into mutual-exclusion evidence.

The NVFS MountTable read dispatcher now uses `pread_bytes_handle` directly,
including its POSIX facade. A diagnostic test exposed that the previous
`pread(..., mut buf)` route could return the right count with unchanged caller
bytes. Owned byte reads preserve NUL/high-bit bytes and ordinary EOF behavior.

## Validation and remaining work

The modern SSpec scenarios in `test/01_unit/os/kernel/loader/` cover source
mutation isolation, owner/generation mismatch, stale references, duplicate
release, slot exhaustion, retained-byte accounting and DBFS/NVFS/NVFS-POSIX
acquisition. The existing authenticated launch argument scenario exercises the
signed NVFS binding, initial argv/envp construction and loader token boundary.

The diagnostic seed producer SHA-256 was
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`.
Flags: `--mode=interpreter --no-cache --no-db --no-session-daemon --sequential
--assert-ran`, one file per invocation, with `SIMPLE_LIB` set to this worktree's
absolute `src` directory. Results: registry 4/4, source acquisition 3/3,
existing exact-byte reread 2/2, authenticated launch argument boundary 3/3;
zero skipped/dropped examples. These are diagnostic, not self-hosted or guest
qualification. No compiler or Phase2 producer was rebuilt.

QEMU RV64 TCG admission on macOS passed the advertised-accelerator and execution
probes with QEMU 10.2.2 (binary SHA-256
`cbe5769bb7c57826582d8363eb0b84ca73c63e8ee8bbcaa611e7b465d86469b5`).
The canonical matrix preflight remains blocked by missing
`build/os/simpleos_riscv64_smf_fs.elf` and an unadmitted diagnostic spec runtime.
There is no guest execution receipt for this change or #5231 argv support.

Next owners: accept compiler-produced anonymous images under real delegated
development-execution or signed artifact authority, bind them to the existing
one-shot admission/scheduler path, enforce aggregate process budgets, replace
ARM64/x86 mutex stubs, and run memory/file policy parity plus retirement in the
guest. Keep the SOSIX memory default disabled until those owners and evidence
exist. Reuse `scripts/check/check-sosix-qemu-matrix.shs --guest riscv64 --preflight`
with `SIMPLE_QEMU_ACCELERATOR=tcg` and an admitted self-hosted runtime for the
host-ready handoff.
