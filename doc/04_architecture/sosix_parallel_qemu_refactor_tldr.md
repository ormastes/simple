# SOSIX Refactor and Multi-Host QEMU Architecture — TLDR

SOSIX becomes the single typed, asynchronous host-service boundary, while one
QEMU descriptor/evidence contract proves six SimpleOS guest architectures on
Linux, Windows, macOS, and FreeBSD without turning unavailable rows into PASS.

## Core Shape

- `os.sosix.core` owns generation-safe operations, completion, cancellation,
  deadlines, and notification wakeups; POSIX is a compatibility adapter.
- WM/GUI/Web/Draw IR/Engine2D keep rendering semantics. SOSIX exposes batched
  display, input, timer, configuration, file, process, and library services.
- One `QemuLaneSettingsV1` lowers each host/guest row; every result is a
  provenance-bound `QemuEvidenceBundleV1` proving boot, mount, target-side
  `ls`, and an arbitrary filesystem program.
- Matrix PASS is derived only from a closed collector-verified receipt whose
  manifest, status, artifacts, clean source, transcript, and program digests
  plus firmware path/version/hash/ordered boot stages are rechecked; path
  strings and caller-set booleans are never proof.
- Large storage resolves env, workspace setting, then `$HOME/.simple`; this
  host's workspace setting selects `/mnt/data/.simple`.
- Missing media, pure-Simple provenance, native host access, or correlated
  evidence leaves the aggregate blocked. TCG proves correctness, not native
  acceleration.

## Operational Notes

- startup: snapshot host configuration and load libraries once.
- hot path: one present per surface/frame; queued input; no per-pixel host calls.
- invalidation: operation, surface, queue, and evidence generations reject stale
  completion and replay.
- evidence: exact argv, accelerator, hashes, nonce, transcript, and guest
  receipts are mandatory.

## Open Next

- [Full architecture](sosix_parallel_qemu_refactor.md)
- [Detailed design](../05_design/sosix_parallel_qemu_refactor.md)
- [Parallel agent plan](../03_plan/agent_tasks/sosix_parallel_qemu_refactor.md)
- [QEMU operator guide](../07_guide/platform/simpleos/sosix_qemu_shared_settings.md)
- [Current blockers](../08_tracking/bug/sosix_qemu_matrix_media_and_selfhost_blockers_2026-08-11.md)
