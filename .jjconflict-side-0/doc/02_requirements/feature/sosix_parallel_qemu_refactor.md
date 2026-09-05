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

Current requirement baseline (2026-08-12): the immutable collector is
**0 PASS / 24**; every narrower success remains diagnostic until its complete
release evidence bundle is admitted.

## Out of scope for the first filesystem slice

GDS/RDMA, network, USB, physical-board acceptance, and unrestricted POSIX from CUDA.
