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
