# SOSIX Parallel QEMU Refactor Requirements

**Selected:** explicit user scope, 2026-08-11

## Functional requirements

- REQ-SQ-001: Provide one reusable typed QEMU settings/descriptor contract for all host and guest lanes.
- REQ-SQ-002: Refactor SOSIX around typed asynchronous operations, completions, cancellation, deadlines, capabilities, buffers, and compatibility adapters.
- REQ-SQ-003: Cover Windows, Linux, macOS, and FreeBSD host classifications without converting unavailable rows to PASS.
- REQ-SQ-004: Cover x86, ARM, and RISC-V guests at both 32 and 64 bits.
- REQ-SQ-005: Boot each guest through its board-representative firmware path and retain a correlated serial transcript.
- REQ-SQ-006: Mount the intended filesystem and execute an in-guest directory listing.
- REQ-SQ-007: Execute at least one arbitrary program loaded from the guest filesystem on every guest row.
- REQ-SQ-008: For compiler-in-filesystem rows, execute target-native Simple, print its version, compile `hello.spl`, and run the result in guest.
- REQ-SQ-009: Provide reusable setup/check/run scripts and operator documentation for other agents.
- REQ-SQ-010: Preserve POSIX file offset and errno semantics through the refactor.
- REQ-SQ-011: Emit fail-closed evidence bundles with exact provenance, argv, hashes, results, and artifacts.
- REQ-SQ-012: Keep postponed macOS evidence open with an authoritative resume plan.
- REQ-SQ-013: Resolve large storage from `SIMPLE_BIG_STORAGE_ROOT`, a workspace-local setting, or `$HOME/.simple` in that priority order; configure this host for `/mnt/data/.simple`.
- REQ-SQ-014: Refactor WM and renderer host access behind typed display, input, timer, configuration, file, process/IPC, and library capabilities while keeping Draw IR/layout/raster/GPU semantics in their canonical owners.
- REQ-SQ-015: Use canonical asynchronous SOSIX operations for deferred host work, with notification-based synchronous adapters only at compatibility boundaries.
- REQ-SQ-016: Keep research, requirements, architecture, design, QEMU operator guidance, Codex/Claude/Gemini SPipe instructions, and feature/layer expert knowledge synchronized with the canonical wrappers and current matrix status.
- REQ-SQ-017: Distinguish diagnostic guest capability from release admission; no diagnostic transcript may change a matrix cell to PASS without clean source, compiler, firmware, nonce, and collector provenance.
- REQ-SQ-018: Provide true FAT32 `read_at`/`write_at` primitives that preserve the sequential cursor, support overwrite and extension with zero-filled holes, reject overflowing or non-FAT32 file sizes before mutation, and persist returned metadata.
- REQ-SQ-019: Give every live FAT32 open-file description a monotonic nonzero identity; dup and fork aliases share that identity and cursor, close retires only the last alias, task exit retires remaining aliases, and stale identities fail closed.
- REQ-SQ-020: Retain the concrete FAT32 positioned backend in the production syscall 134/135 route while keeping registry installation explicit; accept evidence only after a receipt-bound pure-Simple runtime, strong linked shim symbols, and the focused owner suite pass once.
- REQ-SQ-021: Provide binary-safe DBFS and NVFS positioned primitives with short EOF reads, overwrite and suffix preservation, sparse zero-filled extension, invalid-range rejection, device persistence, and no sequential-cursor mutation.
- REQ-SQ-022: Route SOSIX NVFS and DBFS positioned backends only through live monotonic MountTable virtual file objects; reject raw, retired, ambiguous, and cross-filesystem identities.
- REQ-SQ-023: Build and boot the current device-backed `nvfs-dbfs-backed-v1` SimpleOS root twice under QEMU, proving VFS installation, byte-exact positioned I/O, and reboot persistence through source-matched Stage-4 runtime, kernel, image, QEMU, and transcript identities.

REQ-SQ-018 through REQ-SQ-020 were selected explicitly by the 2026-08-16
scoped recovery continuation. They complete the host-independent positioned-I/O
implementation but do not promote a QEMU matrix row without live guest proof.

REQ-SQ-021 through REQ-SQ-023 were selected explicitly by the subsequent
NVFS/DBFS continuation. The provider name is a claim boundary: it records the
current DBFS-backed NVFS facade and does not claim the separate native NVFS
engine is the on-disk namespace owner.

Current requirement baseline (2026-08-12): the immutable collector is
**0 PASS / 24**; every narrower success remains diagnostic until its complete
release evidence bundle is admitted.

## Out of scope for the first filesystem slice

GDS/RDMA, network, USB, physical-board acceptance, and unrestricted POSIX from CUDA.
