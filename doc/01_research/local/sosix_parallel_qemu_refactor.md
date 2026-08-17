# SOSIX parallel QEMU refactor — local research

**Date:** 2026-08-11
**Scope:** current `ormastes/simple` worktree and retained QEMU artifacts
**Status:** 2026-08-11 evidence snapshot; current corrections follow

## 2026-08-16 correction

The observations below are retained as the original 2026-08-11 research
snapshot, not as claims about the current tree. In the current continuation,
the restored SOSIX FS slice defines a true positioned-I/O backend contract but
does **not** contain a FAT32 positioned adapter: `SharedFat32Driver` still
exposes only cursor-based `read`/`write`, and the live kernel trap path has not
adopted the new positioned owner/backend state. The invalid historical adapter
was deliberately not retained. Likewise, the current canonical release ledger
accepts only Linux x86_64, ARM64, and RV32 (3/24); other earlier Linux runs are
diagnostic or blocked, not release PASS evidence. The current implementation
and unblock commands are authoritative in the agent plan, platform guide, and
remaining-owners tracker linked below.

## 2026-08-16 positioned-I/O continuation

The correction above records the state before this scoped continuation. The
current lane now adds FAT32 explicit-offset primitives, generation-safe
canonical file objects with alias retirement, a concrete owned-copy SOSIX
backend, and production shim retention. Authenticated registry installation is
still explicit and fail closed. Runtime, linked-kernel, and QEMU claims remain
blocked until a receipt-bound source-matched Stage-4 runtime executes the
focused gates; the Rust seed and earlier retained ELF are inadmissible.

## Existing architecture and implementation surfaces

The repository now has one configurable large-artifact owner:
`scripts/qemu/simple-big-storage-root.shs`. Resolution order is
`SIMPLE_BIG_STORAGE_ROOT`, the workspace-local config selected by
`SIMPLE_BIG_STORAGE_CONFIG`, then `$HOME/.simple`. This checkout selects
`/mnt/data/.simple`. `simple-qemu-settings.shs`, host admission, the matrix
runner, FreeBSD media admission, and the evidence collector consume that
owner.

The SOSIX filesystem refactor is centered under `src/os/sosix/core` and
`src/os/sosix/fs`. It includes typed operations/completions, owned-copy IPC
132/133, registered buffers, authenticated request correlation, nonblocking
completion pumping, generation-safe service dispatch, OFD sequencing, and what
the 2026-08-11 snapshot described as a cursor-independent FAT32 positioned
backend. The 2026-08-16 correction above supersedes that last claim: no valid
FAT32 positioned adapter exists today. Legacy raw VFS buffers fail
closed rather than fabricating registered references.

Host UI work is split by semantic ownership. GUI/web still lower through
`DrawIrComposition` and Engine2D; Engine3D remains separate. SOSIX owns the
host-facing lifecycle: bounded display state, headless and synchronous SDL2
adapters, callback-driven hosted input, and typed timer requests for frame
pacing. This does not yet prove Win32, Cocoa, X11, Wayland, or SimpleOS display
producer parity.

## Current QEMU evidence

The matrix contract is four hosts by six guests: x86_32, x86_64, ARM32,
ARM64, RISC-V32, and RISC-V64. Linux diagnostic runs currently prove real
FAT32 directory enumeration and one filesystem-loaded target-native program
for five guests. ARM64 has static root-routing and weak-symbol fixes but its
three-run criterion is exhausted and requires a fresh session.

Windows has a fail-closed native PowerShell six-row wrapper but no real-host
execution. macOS has six explicit postponement receipts, not PASS evidence.
FreeBSD has checksum-pinned offline image admission, but the required base
qcow2 is absent. The content-addressed collector rejects missing, relabelled,
duplicate, unhashed, or weak rows.

None of the Linux runs is release evidence yet: kernels were produced by the
Rust bootstrap seed or lack clean-source/run-nonce correlation. A
cache-preserving pure-Simple deployment attempt reached Stage 2 and exposed a
concurrently incomplete runtime wide-integer migration. The current first C
syntax failure is an undeclared `rt_value_u64`, followed by stale
`RtCoreUInt`/`rt_core_as_heap_uint` uses.

## Local conclusions

1. Shared settings and matrix identities are implemented and reusable.
2. SOSIX async contracts are substantially implemented, but generic POSIX
   positioned I/O and additional host display producers remain incomplete.
3. Five Linux boots are strong diagnostics, not release proof.
4. Pure-Simple compiler deployment is the next lineage gate; QEMU reruns must
   wait for it to avoid repeating non-authoritative evidence.
5. The goal completes only with an immutable 24-row manifest containing real
   host evidence or explicit non-PASS receipts, plus boot/mount/list/program
   correlation for every claimed PASS row.

## Related authoritative artifacts

- `doc/01_research/domain/sosix_parallel_qemu_refactor.md`
- `doc/01_research/local/sosix_gpu_api_extension_final_report.md`
- `doc/01_research/local/sosix_wm_renderer_host_interface.md`
- `doc/04_architecture/sosix_parallel_qemu_refactor.md`
- `doc/05_design/sosix_parallel_qemu_refactor.md`
- `doc/03_plan/sys_test/sosix_parallel_qemu_completion_audit_2026-08-11.md`
- `doc/07_guide/platform/simpleos/sosix_qemu_shared_settings.md`

## 2026-08-16 NVFS/DBFS positioned-I/O research extension

<!-- codex-research -->

Parallel source, driver, and QEMU research found that DBFS already owned the
durable byte store used by both `DbFsDriver` and the current NVFS facades, but
its positioned surface converted through `text`, padded reads past EOF, and
did not expose a binary primitive. `NvfsDriver` rejected nonzero write offsets;
`NvfsPosixDriver` also converted positioned writes through text. Raw driver
handle IDs collide across driver instances and therefore cannot be SOSIX file
object identities.

The accepted owner is the existing `MountTable` virtual handle table. It
allocates monotonically increasing IDs, binds each ID to exactly one mount and
opaque inner handle, and removes the binding on close. NVFS/DBFS SOSIX
backends resolve that table and reject missing, retired, raw, or
wrong-filesystem identities. A second registry was rejected because its close,
duplication, and mount-generation state could diverge from VFS.

The SimpleOS NVFS boot path was probe-only: it recognized the LBA 0
superblock, mounted a hosted in-memory facade, and logged success without
installing a device-backed VFS root. The selected implementation makes the
existing architecture explicit as `nvfs-dbfs-backed-v1`: NVFS superblocks
occupy LBA 0/1, canonical DBFS backing metadata occupies LBA 2/3, and the
device-backed NVFS driver owns LBA 4 onward. This is honest current NVFS
support; it is not a claim that the separate native NVFS engine has replaced
the DBFS backing store.

Live QEMU admission requires a source-matched Stage-4 pure-Simple runtime,
adjacent provenance, runtime receipt, linked kernel, immutable image manifest,
two boots of one private image copy, a byte-exact positioned-I/O marker, and
reboot persistence. The existing FAT32-carrier NVFS marker and RV64 arena
probe are diagnostic only and cannot satisfy this requirement.

Highest-capability review found that the generic x86_64 fs-exec entry never
called `boot_fs_sequence`, so that ELF could not emit the new NVFS
mount/oracle markers. The accepted live owner is a dedicated
`nvfs_positioned_entry.spl` built by the admitted Stage-4 runtime with a closed
entry/target/source/compiler/kernel receipt. Review also required explicit
root-kind shim installation, checksum-valid replica failover, bounded DBFS
materialization, rollback on namespace publication failure, and hashes for
both boot transcripts.

## 2026-08-12 evidence-contract update (append-only)

The current immutable collector remains **0 PASS / 24 non-PASS cells**. Linux
diagnostics now prove nonce-bound boot, FAT mount, real `/SYS/APPS` dirent
enumeration, and filesystem-program execution for x86_32, ARM32, RISC-V32,
and RISC-V64. These transcripts are diagnostic truth only: dirty-source or
incomplete firmware/source-lineage receipts prevent release admission.
x86_64 remains blocked on image payload capacity; ARM64 exhausted its bounded
live repair cycles on FAT/VFS directory-buffer capacity. Windows and FreeBSD
lack native complete receipts; macOS is postponed with explicit non-PASS rows.

The canonical rebuild-only wrapper is
`scripts/check/rebuild-sosix-qemu-media.shs`; it supports closed `--rows`
selection and never launches QEMU. Per-run nonce media uses a private image
clone and target-read `/QEMUNONC.TXT`. A directory-listing PASS requires live
dirent-derived `FS_LS_ENTRY` rows between begin/end markers; fixed names or a
host-side listing are not evidence.
