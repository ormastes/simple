<!-- codex-design -->
# Simple 2D Multiplatform Vulkan Hardening System-Test Plan

This plan extends rather than replaces the existing QEMU, Venus, differential,
and primitive-lane plans. A row is `pass`, `fail`, `blocked`, or `unsupported`;
source readiness is not a pass.

| Requirement | Scenario | Required proof |
|---|---|---|
| QEMU capability is not execution | cached physical HELLO followed by no draw | HELLO receipt has zero render evidence; attempted promotion is rejected |
| Device DrawIR execution | bounded rect/text/image composition | matching request/completion/run/frame, Vulkan fence, positive identity/handle, `device_readback`, command coverage, exact CPU parity |
| Runtime safety | discovery + render + ProcessingIR leases overlap and release | non-final release preserves device; final release cleans only after idle/quarantine cleanup |
| Native dispatch safety | nominal and mixin/duck render-target call shapes | nominal implementation dispatches safely; no-vtable shape is explicit adapter/reject, never SIGILL/hidden fallback |
| ARM input | keyboard left/right Ctrl/Alt, pointer/click/drag/wheel | ordered normalized event + WM target/action/state epoch in one atomic receipt |
| ARM audio | VirtIO-SND playback and capture in a requested scenario | stream/session/generation and completion/hash join the same frame receipt; stale/replay rejects |
| DrawIR fonts/animation | two or more animation frames containing text | semantic text, selected font/batch/atlas status, distinct frame checksums, device-readback capture |
| Performance | post-oracle accelerated QEMU run | 20 warm samples, nearest-rank p95, daemon/QEMU/combined RSS, exact profile/argv/device |
| macOS | approved-host run | native evidence or explicit unsupported on non-macOS; no Linux surrogate pass |
| UNO Q | board-attached run | physical identity and native device lifecycle receipt or explicit `board-not-connected`/runner blocked result |

Test owners must preserve the canonical `simpleos_2d_showcase`,
`simpleos_io_audio`, `simpleos_qemu_host_gpu_2d`, VirtIO discovery, and Vulkan
instance-reuse test surfaces. New tests are added only after the corresponding
interface owner exists; their generated manuals mirror under `doc/06_spec` and
must contain real receipt assertions. Differential traces can compare semantic
state transitions, but they do not replace exact device pixels for a Vulkan
promotion.

Current expected outcomes: the Linux/ARM render scenarios remain `blocked`
until native dispatch and first submission are proven; macOS is `unsupported`
on this host; UNO Q is `blocked` until attached. Existing contract/self-test
passes retain their narrower status and must not be rewritten as live results.
