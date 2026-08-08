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

## Current accepted source and open evidence

The 2026-07-27 source checkpoint repairs the two later review findings without
promoting runtime evidence:

- canonical package CSS emits real newlines and complete traffic-control,
  window-state, resize/hot-corner, dialog/form, tooltip/tree, taskbar, and
  responsive structure while the Aetheric package remains the paint/material
  authority;
- the retained Metal session device is the single material/readback identity,
  and the host validates one ordered receipt for every independently derived
  Draw IR material request; missing, duplicate, extra, reordered, unfulfilled,
  mixed, or tuple-mismatched receipts fail closed;
- sub-opaque selected Metal fails before dispatch until a true GPU-only
  parent-seeded delta path exists; it cannot claim success through a CPU mirror;
- the hosted browser binds its trusted renderer inside the production WM route,
  keeps address/title commands on the compositor, routes page pointer/key/text
  and active-animation work through that renderer, and re-submits the resulting
  external frame; a scoped, comment-filtered source contract rejects private
  or direct update routes. Address Backspace validates complete UTF-8 before
  deleting one trailing scalar and leaves malformed drafts unchanged. CPU and
  Draw IR input text share computed transform/RTL/alignment/vertical placement,
  theme foreground, and content/ancestor clipping; Engine2D restores the
  enclosing clip through its canonical text/font routes. Supported single-line
  inputs also lower stable UTF-8 selection boundaries into computed-color
  selection and caret rectangles around the canonical text command; readonly,
  disabled, prevented-default, chrome-focus, blink, reveal, and invalid-UTF-8
  behavior remains fail-closed. Textarea overlays remain explicitly open;
- the macOS full-CLI admission boundary uses a normalized v2 history verifier
  and tracked fail-closed trust-root gate. An Endpoint Security exec/fork/exit
  collector candidate now exists and passed bounded static review plus fresh
  clean-revision source verification: Swift `-lbsm` link/self-test, builder
  self-test, focused boundary/full-CLI/GPU contracts, direct-env scope guards,
  and explicit unavailable-policy `--exec-verified` exit 125. Policy remains
  unavailable, so this is not live admission or GUI evidence.

These are source contracts, not pixels or events. The native macOS row still
needs provisioned signing/entitlement, separately reviewed prepared/admitted
pins, and the exact admitted runtime. The
x86_64 QEMU row still needs an admitted kernel/disk/frozen manifest plus
`grub-mkstandalone`; ARM64 still needs an admitted ELF/FAT/frozen manifest and
fresh guest receipts. Windows Vulkan/SIMD and Linux
Vulkan/RenderDoc/SIMD remain prepared-host rows. Every unavailable row remains
open and fail-closed. The current QEMU contract review and exact repair gates
are tracked in
`doc/08_tracking/bug/wm_glass_qemu_evidence_contract_p1_2026-07-27.md`.

## Evidence and failure handling

Successful production admission must retain exact source/binary revision,
theme identity, viewport, selected backend, fallback/capability state,
framebuffer or device readback provenance, checksum, artifact paths, and the
first unavailable proof rung. Vulkan and Metal additionally require device
identity, submission/completion, device-origin readback, and CPU-oracle parity.
QEMU requires the canonical entry, independent framebuffer capture, and
ordered guest input evidence.

Until those artifacts exist, `require_wm_glass_theme_evidence()` intentionally
fails the executable system scenario. The focused source repairs above have
independent review acceptance, but the available repository launcher is not an
admitted source-matched pure-Simple runtime and no bootstrap was authorized.
The earlier suppressed-runner diagnostic remains tracked in
`doc/08_tracking/bug/sspec_runner_suppresses_child_failure_diagnostic_2026-07-26.md`.
A fresh admitted pure-Simple focused PASS plus native host/device/QEMU artifacts
is still required; this manual and the source reviews cannot be treated as a
system PASS.
