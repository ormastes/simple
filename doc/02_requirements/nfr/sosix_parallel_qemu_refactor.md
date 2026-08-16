# SOSIX Parallel QEMU Refactor NFRs

- NFR-SQ-001: No busy-spin wait in SOSIX synchronous adapters or device APIs.
- NFR-SQ-002: No raw pointers in shared request/completion contracts; use slot/generation references.
- NFR-SQ-003: Missing firmware, emulator, accelerator, image, marker, receipt, or program output fails closed.
- NFR-SQ-004: TCG proves correctness only; native timing requires KVM, HVF, or WHPX in the retained executed argv.
- NFR-SQ-005: Each lane uses bounded timeouts, isolated artifacts, and at most three distinct repair cycles.
- NFR-SQ-006: Large QEMU media and scratch use the configurable large-storage root; this host uses `/mnt/data/.simple`, other hosts default to `$HOME/.simple`, and cleanup is explicit and lane-scoped.
- NFR-SQ-007: Tests use independent absolute oracles and include sabotage evidence; file presence and source grep are insufficient.
- NFR-SQ-008: New Simple code meets 80% branch coverage where measurable and passes lint/duplicate/dependency gates.
- NFR-SQ-009: QEMU settings and evidence schemas are versioned and deterministic across agents and hosts.
- NFR-SQ-010: Operator manuals have zero stubs and explain blocked/unavailable rows and exact resume commands.
- NFR-SQ-011: No per-pixel, per-primitive, or repeated hot-frame environment/file/process SOSIX calls; frames and events are batched and configuration is snapshotted at startup.
- NFR-SQ-012: Display completions bind surface generation and frame sequence; stale, duplicate, canceled, or reset completions fail closed.
- NFR-SQ-013: Knowledge surfaces state the current immutable matrix count explicitly; as of 2026-08-12 it is **0 PASS / 24**, regardless of narrower diagnostic successes.
- NFR-SQ-014: Positioned filesystem data remains owned bytes across SOSIX/VFS/driver boundaries; binary payloads never round-trip through `text`.
- NFR-SQ-015: Qualified NVFS QEMU evidence uses one private image copy for both boots, bounded execution, a closed dedicated-entry kernel receipt, exact runtime/kernel/image/QEMU/transcript hashes, and no implicit build, prebuilt fallback, marker-only promotion, or Rust-seed substitution.
