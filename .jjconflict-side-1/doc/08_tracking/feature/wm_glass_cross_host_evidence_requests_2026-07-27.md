# WM glass cross-host evidence requests

**Filed:** 2026-07-27
**Status:** request
**Priority:** P0
**Current-host lane:** active-local
**External-host lanes:** postponed-external-host

## Boundary

The current macOS source lane remains active. The following requests postpone
only evidence that requires Windows, Linux, or a current admitted QEMU guest.
They are required rows, not exclusions and not PASS.

Every row must exercise the same canonical chain:

`Aetheric package -> Simple Web computed style -> DrawIrComposition ->
Engine2D glass material -> backend readback -> native events`.

Generic clear/fill, synthetic events, stale captures, Electron-only pixels,
Rust-seed execution, and CPU fallback cannot satisfy these requests.

## Common admission receipt

Each external host must retain one `evidence.env` with:

- `status=pass` and a platform-specific stable reason;
- source commit and dirty-state receipt;
- self-hosted pure-Simple runtime kind, version, and SHA-256;
- Aetheric manifest and glass-material SHA-256;
- Draw IR composition identity and command count;
- requested and executed backend identity;
- device-origin readback source, dimensions, pixel count, and SHA-256;
- CPU/SIMD oracle SHA-256 and exact parity status;
- focus, pointer, keyboard, click, frame-commit, and damage receipts;
- monotonic event sequence and frame identifiers;
- regular capture paths with SHA-256;
- zero skipped commands and zero unapproved fallback count.

Any absent, stale, malformed, synthetic, or mismatched field is `fail`, never
`skip` or an inferred PASS.

## Active fail-closed handoff matrix

Every row below remains required and open.  A listed command is a resume
command, not evidence that it has run; a missing checker is an implementation
prerequisite and must fail closed until it exists.  No bootstrap or Rust-seed
binary is permitted at any point in these rows.

| Row | Required prepared host/capability and first missing prerequisite | Exact resume command | Retain before review | Owner | Final reviewer |
|---|---|---|---|---|---|
| `MAC-WM-GLASS-LOCAL-001` (native CPU/NEON/Metal) | macOS with a reviewed Endpoint Security exec/fork/exit collector and admitted trust-root branch, reproducible collector provenance, approved signing team and entitlement, signed policy-pinned collector, and source-matched canonical full CLI GUI driver carrying the Winit marker. The collector passed clean-revision source verification and independent review, including both self-tests, focused contracts, and explicit unavailable-policy exit 125. Policy remains unavailable; no signed collector, canonical driver, or live evidence exists. | Provision signing identity/entitlement and review a `prepared` policy with source/toolchain/argv/env pins while output/manifest hashes stay unavailable; build and review the collector candidate; separately admit its exact output/manifest hashes; only then produce and admit the canonical driver before live widget/Web evidence. Do not rerun already-green source gates as a substitute for admission. | manifest-v3/launcher receipt, OS-backed admitted driver/execution-tree proof, source/runtime/provider hashes, native PID/window-owner and event receipts, CPU/NEON oracle, per-material GPU-only Metal receipts, device readback, captures, timing, RSS. Receipt `801caf` is device-operation evidence only, not widget/web/live-product proof. | prepared macOS collector implementation/security provisioning owner | independent highest-capability reviewer |
| `FR-WM-GLASS-WIN-0001` | physical Windows x86_64 with a Vulkan-capable driver, native event path, and admitted self-hosted `simple.exe`; the checker and admitted runtime are missing. | `sh scripts/check/check-wm-glass-windows-vulkan-evidence.shs` after creating the checker and admitting the exact runtime. | `build/evidence/wm-glass/windows-vulkan/evidence.env`, Vulkan readback/captures, x86 SIMD oracle, device/library identity, ordered native events, timing/RSS. | prepared Windows host operator | independent highest-capability reviewer |
| `FR-WM-GLASS-LINUX-0001` | physical Linux x86_64 with Vulkan, RenderDoc, native display server, and admitted self-hosted runtime; the checker, runtime, and current `RDOC` capture are missing. | `sh scripts/check/check-wm-glass-linux-vulkan-evidence.shs` after creating the checker and admitting the exact runtime. | `build/evidence/wm-glass/linux-vulkan/evidence.env`, regular-file `RDOC`, device readback/captures, x86 SIMD oracle, ordered native events, timing/RSS. | prepared Linux host operator | independent highest-capability reviewer |
| `FR-WM-GLASS-X86-QEMU-0001` | host with `grub-mkstandalone`, x86_64 QEMU, OVMF/firmware, and an admitted source-matched kernel/disk/manifest; the current canonical guest artifacts and host tool are missing. | `BUILD_DIR=build/simpleos_wm_fullscreen_evidence SIMPLE_BIN=<admitted-simple> sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | frozen source/build manifest, kernel/disk/runtime hashes, serial and QMP logs, `pmemsave` baseline/maximized/restored PPMs and hashes, SSE2 oracle, ordered IRQ/WM/frame/damage receipts, timing/RSS. | `/root/x86_qemu_owner` | independent highest-capability reviewer |
| `FR-WM-GLASS-ARM-QEMU-0001` | host with QEMU AArch64 and firmware plus admitted source-matched ARM64 ELF, FAT disk, and manifest; all live guest artifacts/receipts are missing. | `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` then `sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` | frozen source/build manifest, ELF/FAT/runtime hashes, serial/QMP logs, baseline/post-input RAMFB captures and hashes, NEON oracle, VirtIO order/WM/frame/damage receipts, timing/RSS. | `/root/arm_qemu_owner` | independent highest-capability reviewer |

The RV64 QEMU input/render row is also active and fail-closed under the
SimpleOS host-GPU handoff: it requires a current admitted RV64 ELF, modern PCI
VirtIO keyboard/mouse, QMP, and an RV64 CPU parity oracle; resume with
`bin/simple os build --scenario=riscv64-display-smoke` then
`scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input`.
Retain its frozen manifest, ELF hashes, serial/QMP logs, RAMFB captures,
PCI/ISR/event receipts, parity result, timing, and RSS.  The prepared RV64
host operator owns the row; an independent highest-capability reviewer must
approve it.  It is not a substitute for either ARM64 or x86_64 evidence.

## FR-WM-GLASS-WIN-0001 — Windows Vulkan and SIMD proof

**Status:** postponed-external-host

Target a physical Windows x86_64 host with a Vulkan-capable driver and an
admitted `simple.exe`.

TODO:

1. Add `scripts/check/check-wm-glass-windows-vulkan-evidence.shs`.
2. Render the canonical Aetheric scene through pure-Simple Web and Engine2D.
3. Capture Vulkan device readback and the x86 SIMD oracle from the same Draw IR.
4. Drive native focus, pointer, key, text, click, maximize, and restore events.
5. Retain bit-exact capture comparison plus device/event receipts.

Electron and D3D12 evidence may be diagnostic companions but cannot replace
the pure-Simple Vulkan row.

## FR-WM-GLASS-LINUX-0001 — Linux Vulkan, RenderDoc, and SIMD proof

**Status:** postponed-external-host

Target a physical Linux x86_64 host with Vulkan, RenderDoc, a native display
server, and an admitted self-hosted runtime.

TODO:

1. Add `scripts/check/check-wm-glass-linux-vulkan-evidence.shs`.
2. Reuse the canonical Linux Vulkan setup only as transport; bind it to the
   Aetheric Web/Draw-IR glass scene.
3. Capture a valid regular-file `RDOC` artifact and device readback.
4. Compare the Vulkan frame bit-exactly with the x86 SIMD oracle.
5. Retain native focus, pointer, keyboard, click, frame, and damage receipts.

Browser-only or generic solid-fill Vulkan evidence is insufficient.

## FR-WM-GLASS-X86-QEMU-0001 — x86_64 SimpleOS rendering and events

**Status:** postponed-external-host

Target a host with `grub-mkstandalone`, QEMU x86_64, firmware, and a
source-matched admitted SimpleOS kernel/disk.

TODO:

1. Run `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs`.
2. Retain kernel, disk, build-manifest, runtime, and frozen-source receipts.
3. Capture baseline, maximized, and restored PPMs with SHA-256.
4. Correlate QMP focus/pointer/key make-break events with guest IRQ, WM state,
   framebuffer revision, frame commit, and damage receipts.
5. Prove SSE2 parity against the canonical CPU glass oracle.

Old diagnostic kernels and degraded/fallback content are invalid.

## FR-WM-GLASS-ARM-QEMU-0001 — ARM64 SimpleOS rendering and events

**Status:** postponed-external-host

Target a host with QEMU AArch64, firmware, and a source-matched admitted ARM64
kernel, FAT disk, manifest, and frozen-source receipt.

TODO:

1. Run the attested guest build on the target host, then execute
   `scripts/check/check-simpleos-arm64-qmp-input-evidence.shs`.
2. Retain before/after RAMFB captures and SHA-256.
3. Prove NEON parity against the canonical CPU glass oracle.
4. Correlate ordered QMP pointer and keyboard events with VirtIO input, WM
   state, framebuffer damage, and monotonic frame commits.
5. Reject `canonical-kernel-missing`, stale disks, synthetic events, and
   presentation-only VirtIO-GPU as completion.

## Current macOS lane — not postponed

`MAC-WM-GLASS-LOCAL-001` remains active locally:

- obtain an admitted pure-Simple runtime without substituting the Rust seed;
- run the focused CPU material specs;
- produce the same-scene NEON and Metal device readbacks;
- retain native macOS focus/pointer/key/click/frame receipts;
- compare CPU, NEON, and Metal captures through the shared material identity.

Metal backend creation falling back to CPU remains a failure, not a reason to
move this row into the external-host backlog.

## Links

- Plan: `doc/03_plan/agent_tasks/wm_glass_theme_host_simpleos.md`
- Test plan: `doc/03_plan/sys_test/wm_glass_theme_host_simpleos.md`
- Architecture: `doc/04_architecture/wm_glass_theme_host_simpleos.md`
- Design: `doc/05_design/wm_glass_theme_host_simpleos.md`
- Contract: `test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl`
- Manual: `doc/06_spec/03_system/check/wm_glass_cross_host_evidence_request_spec.md`
