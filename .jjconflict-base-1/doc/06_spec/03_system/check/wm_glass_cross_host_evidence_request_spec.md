# WM Glass Cross-Host Evidence Requests

## Purpose

This contract keeps platform-dependent WM glass work visible without claiming
that it ran on the current host. Windows, Linux, x86 QEMU, and ARM QEMU remain
required, fail-closed request rows. The current macOS source/evidence lane stays
active.

The authoritative request ledger is:

`doc/08_tracking/feature/wm_glass_cross_host_evidence_requests_2026-07-27.md`.

## Operator flow

1. Select exactly one target host row.
2. Check out the source commit named by the evidence run.
3. Use an admitted self-hosted pure-Simple runtime; reject the Rust seed.
4. Render the canonical Aetheric Web/Draw-IR glass scene.
5. Capture the requested backend and CPU/SIMD oracle from the same scene.
6. Drive native focus, pointer, keyboard, click, and window-state events.
7. Retain device readback, capture hashes, event sequence, frame commit, and
   damage receipts.
8. Mark the row PASS only when every common admission field is present and
   mutually consistent.

## Platform requests

| Request | Target | Required backend/evidence | Current status |
|---|---|---|---|
| `FR-WM-GLASS-WIN-0001` | Windows x86_64 | Vulkan, x86 SIMD, native Windows events | postponed-external-host |
| `FR-WM-GLASS-LINUX-0001` | Linux x86_64 | Vulkan, RenderDoc, x86 SIMD, native display events | postponed-external-host |
| `FR-WM-GLASS-X86-QEMU-0001` | SimpleOS x86_64 | SSE2 oracle, PPM captures, correlated QMP/guest events | postponed-external-host |
| `FR-WM-GLASS-ARM-QEMU-0001` | SimpleOS ARM64 | NEON oracle, RAMFB captures, correlated QMP/VirtIO events | postponed-external-host |
| `MAC-WM-GLASS-LOCAL-001` | Current macOS host | CPU, NEON, Metal, native macOS events | active-local |

## Acceptance boundary

A platform row is not complete merely because tools or drivers exist. PASS
requires the same canonical Aetheric material to survive:

`package -> Web computed style -> DrawIrComposition -> Engine2D backend ->
device readback -> native event/frame receipts`.

The following are diagnostic only:

- generic fill/clear or alpha fixtures;
- synthetic event fixtures;
- stale or source-unbound captures;
- CPU fallback presented as Vulkan or Metal;
- Electron-only pixels;
- presentation-only VirtIO-GPU;
- any Rust-seed execution.

## Executable checks

The system spec checks that:

1. macOS remains active rather than being hidden in the external backlog;
2. Windows and Linux requests name their backend and native-event work;
3. x86 and ARM QEMU requests name their guest artifacts and event correlation;
4. the common receipt requires source, runtime, material, device, capture,
   parity, and native-event provenance;
5. all four external rows remain explicitly postponed and fail closed;
6. every request is registered in the canonical feature database.

Run, once an admitted pure-Simple test runner is available:

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl \
  --mode=interpreter --clean --fail-fast
```

Until that runtime exists, source review and `git diff --check` validate only
the contract shape, not an executable PASS.
