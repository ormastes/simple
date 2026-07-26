# WM Glass Theme on Host and SimpleOS

This manual accompanies
`test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl`.
It describes the intended production evidence flow. The executable scenario
currently fails closed until current-source host and SimpleOS/QEMU evidence is
available; this manual is not an execution receipt.

Plan and design:
`doc/03_plan/agent_tasks/wm_glass_theme_host_simpleos.md`,
`doc/03_plan/sys_test/wm_glass_theme_host_simpleos.md`,
`doc/04_architecture/wm_glass_theme_host_simpleos.md`, and
`doc/05_design/wm_glass_theme_host_simpleos.md`.

## Primary scenario

1. Load the Stitch glass theme.
2. Render the hosted WM through the canonical `SharedWmScene ->
   DrawIrComposition -> Engine2D` route.
3. Apply glass CSS and widget computed styles.
4. Boot the canonical SimpleOS desktop in QEMU.
5. Capture and compare semantic and framebuffer evidence.

The expected material witness includes the selected package identity, manifest
and material hashes, translucent window fill, normalized gradient, rounded
radius, border, ordered shadows, backdrop request, typography, and active
state. A compatibility renderer, synthetic frame, raw-runtime shortcut, or
stale identity is rejected.

## CPU-composited material source checkpoint

The current source slice lets canonical WM styled rectangles request
`engine2d-cpu-composited-material-v1`. Engine2D samples already-painted CPU
pixels, uses bounded blur and saturation, clips to the rounded shape, and
alpha-composites the package surface or two-stop gradient before its existing
border. If the capability is unavailable, the named solid fallback remains the
required accessible behavior.

For native-safe transport the command color remains opaque
`solid_fallback_rgba`; the translucent `window_fill_rgba` request stays in the
existing `background-color` style and feeds the CPU material helper. Requested
blur 30 is explicitly realized as blur 4, with realized blur/saturation and a
reduction witness. The helper uses `i64` arithmetic and caps output plus
horizontal working storage at 67,108,864 pixels.

The canonical Simple Web source path now preserves the exact opt-in Aetheric
glass stack, rejects unsupported raw layers, emits explicit requested and
bounded-realized material witnesses, and keeps the named opaque command
fallback. Engine2D records a receipt only when CPU glass execution succeeds;
CPU-composited provenance is created after execution only when the complete
Draw IR witness count equals that receipt count. The WM frame validator admits
only the exact solid/CPU reason pairs and lowercase SHA-256 formatting.
The Aetheric typed snapshot and Web shorthand both retain the translucent
`0xCC1F1F21` base plus raw alpha stops `0x14FFFFFF` and `0x06FFFFFF`; the
current material hash is
`0ad3df8e5f6169cb83a2554fbe0823ec470070ae43a47eae701c4f9321cdda37`.
Embedded/offscreen material batches remain receipt-ineligible until they can
sample the already-painted parent backdrop.

This remains source-level CPU semantics. It does not prove CPU-SIMD execution,
Vulkan or Metal device execution, host capture, QEMU capture, device-origin
readback, input-event delivery, timing, or RSS. Those rows require their own
retained immutable artifacts and independent review.

## Evidence and failure handling

Successful production admission must retain exact source/binary revision,
theme identity, viewport, selected backend, fallback/capability state,
framebuffer or device readback provenance, checksum, artifact paths, and the
first unavailable proof rung. Vulkan and Metal additionally require device
identity, submission/completion, device-origin readback, and CPU-oracle parity.
QEMU requires the canonical entry, independent framebuffer capture, and
ordered guest input evidence.

Until those artifacts exist, `require_wm_glass_theme_evidence()` intentionally
fails the executable system scenario. The 2026-07-26 CPU/Web material
checkpoint is **SOURCE PREPARED / UNVERIFIED**: the focused runner exhausted
its three-cycle cap with only `0 passed, 1 failed` and no child diagnostic.
The harness defect is tracked in
`doc/08_tracking/bug/sspec_runner_suppresses_child_failure_diagnostic_2026-07-26.md`.
The available repository launcher identifies as a Rust bootstrap seed, and no
bootstrap was authorized. A fresh pure-Simple focused PASS plus host/device/QEMU
artifacts are still required; this cannot be treated as a system PASS.
