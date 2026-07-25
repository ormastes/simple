# macOS Vulkan/Metal and SimpleOS QEMU Rendering Completion

Updated: 2026-07-24

## Goal

Prove equivalent Simple 2D, web, GUI, vector-font, and event behavior through
Vulkan (MoltenVK) and Metal on macOS, then prove the applicable WM/2D behavior
on SimpleOS under QEMU. Evidence must include real backend initialization,
positive backend identity, device readback, semantic pixel checks, visible
capture, and keyboard/pointer/click delivery. Vector-font evidence must use the
canonical `FontRenderer` path and include the requested 300 DPI configuration.

## Checkpoint and Overall Status

- WIP checkpoint `84397f04ba` (`wip(rendering): checkpoint Vulkan host and WM
  fixes`) is pushed to `origin/main`. It is a recoverable checkpoint, not
  completion evidence.
- The later wrapper-hardening work is rebased in this isolated worktree and
  remains unverified.
- The strict host/QEMU 2D aggregate currently reports **FAIL**. Static source
  prerequisites and prior partial receipts do not substitute for live guest
  framebuffer, bounds, hash, SIMD-runtime, and input receipts.
- The overall goal remains **FAIL / INCOMPLETE**. Vulkan live web, GUI, 300 DPI,
  and host WM must pass before equivalent Metal checks; QEMU WM must follow a
  host-WM PASS.

## Authoritative Lane State

| Lane | State | Current evidence or blocker |
|---|---|---|
| macOS Vulkan environment | PASS | MoltenVK initializes on Apple M4 through `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`. |
| Vulkan vector pipeline creation | PASS (focused only) | A minimal provider probe initialized Vulkan and created the precompiled-SPIR-V pipeline on Apple M4. This does not prove live composite/capture/events. |
| Vulkan vector composite/readback | FIXED, NOT REVERIFIED | Descriptor bindings 0–2 and returned-byte readback are implemented; promoted device execution, fence completion, nonzero exact bytes, and oracle checksum parity still need one fresh proof. |
| Vulkan 2D render/events | FAIL — SAFE PIPELINE REFLECTION FIX NOT REVERIFIED | The Vulkan-enabled provider now compiles and exports raw pointer/length bridges for SPIR-V, push constants, upload, and download. Core-C now packs widened `[u8]` slots in thread-local storage, and the focused runtime/provider compile gates pass. A retained pure-Simple closure was relinked with Apple `ld_new`, the corrected core-C object, and the raw provider bridges. The strict live run advanced through shader-module creation but aborted inside the C `spirv-reflect` parser before a receipt or window. All eight Engine2D SPIR-V source blobs independently pass `spirv-val`, so `ComputePipeline` now derives set-0 storage bindings with a bounds-checked Rust SPIR-V instruction scan instead of the aborting parser. That final fix is formatted but not rebuilt/live-tested because the three-cycle cap is reached. No capture/events exist. |
| Vulkan web render/events | FAIL | No accepted live window/capture/event proof. Asset-root, stamped rerender, readback checksum, bounded failure, exact PID/window capture, and input checks are implemented. |
| Vulkan widget GUI/render/events | FAIL | Earlier 320×240/96 DPI device-frame and font-cache receipts ended before accepted window/event evidence. Exact PID/window capture, Retina backing-scale, checksum, and input fixes are present but unverified. |
| 300 DPI vector GUI | NOT PROVEN | Earlier 1200×900/300 DPI source interpretation exceeded about 1.5 GiB before window discovery. Provider-first `dlopen` reduced the smaller path's RSS, but no 300 DPI live PASS exists. |
| Metal host lanes | PENDING AFTER VULKAN | Do not infer Metal parity from Vulkan or CPU mirrors. Preserve and review the local 2D comparison lane separately. |
| Host WM | FAIL | Source and fail-closed wrapper fixes are present. The contract currently reaches 5/6 through a Rust seed; the negative artifact fixture must be made worktree-independent and live production evidence still needs a qualifying native artifact. |
| QEMU SimpleOS 2D/SIMD | FAIL | The strict aggregate is negative; live guest framebuffer, exact hashes/bounds, event delivery, and runtime SIMD receipts are missing or incomplete. |
| QEMU WM | NOT STARTED | Must follow a host-WM PASS. |

## Bootstrap State

The rendering gates are currently blocked on producing a qualifying full
self-hosted CLI/native artifact, not on the stale primitive-vtable diagnosis:

1. An older bootstrap run passed Stages 2 and 3.
2. Its Stage 4 one-binary build reached approximately **3.3 GiB RSS** and was
   terminated for OOM/resource safety. That path is not accepted as a PASS.
3. Dynload bootstrap cycles 1 and 2 stayed below **1 GiB RSS**, but both were
   blocked because the deployed Stage 3 compiler used stale vtable-owner logic
   and diagnosed primitive owner `i32` incorrectly.
4. The upstream source fix is commit `c120be52f7`
   (`fix(seed): primitive/generic vtable owners fall back to legacy
   module-prefix ownership`).
5. The refreshed Stage 3 compiler passed its sanity probe. Its SHA-256 is
   `35174afcc5aa1a3599f85b3455b77f9a8db538c42b34616ebbf342ffadd5cf17`.
6. Dynload cycle 3 passed the vtable failure and generated the full object
   closure under **1 GiB RSS**, then failed link with 220 unresolved hosted
   runtime symbols. The three-cycle dynload cap is exhausted for this session;
   do not repeat that full-CLI probe.

Do not treat the old Stage 2/3 PASS as proof that the current source or Stage 4
is deployable. Do not retry the 3.3 GiB one-binary path merely to reproduce the
same failure.

## Implemented but Unverified

- The macOS GUI launcher forwards repository asset roots and bounded
  backend/event evidence settings.
- Vulkan web examples rerender after stamped input and cross-check renderer and
  device-readback checksums.
- Web, widget-GUI, and host-WM live wrappers now fail closed, bound RSS/time,
  retain diagnostic output, and reject missing capture/input/device identity.
- Both macOS wrapper contract specs now exist:
  `macos_vulkan_web_live_evidence_contract_spec.spl` and
  `macos_vulkan_gui_widget_live_evidence_contract_spec.spl`. The earlier claim
  that the web spec was missing is stale. The new GUI spec and the hardened
  wrappers have not yet completed their required verification/manual refresh.
- Font probing opens the provider before loading the large font, preventing
  repeated boxed copies when a provider candidate is absent.
- The macOS Vulkan provider exposes storage-buffer bindings 0, 1, and 2 for the
  shared vector-font shader.
- Vulkan font readback uses the canonical returned-byte API.
- Host WM uses stable executor accessors, receiver-local window projection, and
  sequential JSON escaping; its evidence wrapper requires the intended native
  artifact and routed input.

## Exact Next Steps

### 2026-07-24 Safe-Reflection Checkpoint

- Replaced the aborting SPIR-V reflection path with bounded direct parsing and
  added set-zero, contiguous-binding, malformed-module, and raw-pointer guard
  coverage. Focused Rust results: 7 parser tests and 3 raw-ABI guard tests
  passed.
- Rebuilt and staged the Vulkan runtime provider; its build now fails closed
  unless all four raw Engine2D ABI symbols are exported.
- The strict pure-Simple 4K/300-DPI Vulkan launch advanced past the former
  `spirv-reflect` abort, but MoltenVK rejected the submitted shader with
  `SPIR-V to MSL conversion error: Currently no block to insert opcode.` The
  gate therefore remains FAIL (`launched-process-missing`); see
  `doc/09_report/macos_vulkan_2d_live_evidence_safe_reflect_2026-07-24.md`.
- Next isolate the exact submitted byte stream at the raw compile boundary and
  validate that captured stream with `spirv-val`/SPIRV-Cross. Do not proceed to
  Vulkan web/GUI/WM or Metal until this first live 2D gate passes.
- Follow-up capture isolated the failure to the eleventh compile call: the
  vector-font head/tail append loop corrupted raw iterated bytes at the generic
  tagged `array.push` boundary. The byte-array concat fix now emits the exact
  pinned 10,884-byte module and passes `spirv-val`. The next blocker is the
  freshly built closure: its default link omits explicit provider dependencies,
  and diagnostic provider injection traps in `VulkanBackend.clear` because the
  backend receiver is nil. Fix the source-root/module identity or native-link
  closure so the strict wrapper can launch an explicitly provider-linked
  binary; then rerun the live gate in a fresh bounded session.

1. In a fresh bounded verification session, run the focused
   `storage_binding_numbers` unit tests and rebuild the Vulkan-enabled runtime
   provider. Require the four raw Engine2D ABI exports. Build the pure-Simple
   `macos_vulkan_session_live_probe.spl` and strict harness with a compiler that
   includes the `nil.id` semantic-build fix; the currently deployed compiler
   cannot resolve a fresh closure. Require session status 0, nonempty device
   identity, and no `shader-*`/`pipeline-*` label. If `ld_classic` stalls,
   relink retained objects with Apple `ld_new` plus the Command Line Tools SDK;
   do not use dynamic-lookup. Separately replace the unconditional
   `-ld_classic` compiler policy with a tested current-linker option. Do not
   rebuild again in the current session: all three targeted cycles have been
   consumed.
2. Launch Vulkan 2D first. Require a real MoltenVK device, positive handle,
   same-frame device readback, durable before/after capture, vector-font
   identity at 300 DPI, and ordered focus/pointer/key receipts.
3. Verify the hardened web, widget-GUI, and WM contract specs once and generate
   or refresh their mirrored manuals. Require real assertions and zero
   placeholder passes.
4. Run the focused Vulkan font composite/readback proof once. Require promoted
   Vulkan execution, fence completion, positive backend handle, nonzero exact
   readback bytes, and matching device/oracle checksums.
5. Run Vulkan web and widget-GUI live gates. Require visible capture plus focus,
   keyboard/text, pointer, and click receipts. Then repeat widget GUI at
   300 DPI with the selected vector-font identity and cold/warm cache receipts.
6. Run the host-WM production fullscreen gate and require the native artifact,
   semantic capture, taskbar/window evidence, and routed input.
7. Only after Vulkan passes, run equivalent Metal 2D/web/GUI/WM rendering and
   event gates and review the existing local agent's 2D comparison commit
   without absorbing its uncommitted work.
8. Run the strict QEMU SimpleOS 2D/SIMD aggregate until it has real guest
   framebuffer, dimensions/bounds, exact hashes, input delivery, and runtime
   SIMD receipts. Then run QEMU WM after host WM passes.
9. Run rendering coupling, direct-runtime, numbered-artifact, spec-layout,
    compiler/core/lib/MCP/LSP, and scoped production verification gates.
    `STATUS: PASS` is required before a completion commit or release.
10. Commit only the isolated verified lane, fetch/rebase linearly onto
    `main@origin`, apply the file-count guard, set `main`, and push.

## Required Evidence and Documentation

- `doc/04_architecture/shared_multilingual_gpu_fonts.md`
- `doc/05_design/shared_multilingual_gpu_fonts.md`
- `doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`
- `doc/07_guide/lib/shared_multilingual_gpu_fonts.md`
- `doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.md`
- `doc/06_spec/02_integration/rendering/vulkan_font_composite_classification_spec.md`
- `test/01_unit/lib/engine/font_ffi_spec.spl`
- `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl`
- `test/01_unit/os/compositor/host_compositor_entry_spec.spl`
- `doc/06_spec/01_unit/os/compositor/host_compositor_entry_spec.md`
- `test/03_system/check/macos_vulkan_web_live_evidence_contract_spec.spl`
- `test/03_system/check/macos_vulkan_gui_widget_live_evidence_contract_spec.spl`
- Mirrored manuals for both macOS Vulkan wrapper specs under
  `doc/06_spec/03_system/check/`

Refresh shared font documentation only after the current provider behavior is
proven; do not preserve obsolete SPIR-V hash/size or rejected semantic claims.

## Ownership and Stop Conditions

| Lane | Owner | Merge rule |
|---|---|---|
| Host Vulkan web/GUI/font provider | Primary rendering agent | Merge only after live device/capture/event PASS. |
| Host/QEMU 2D Vulkan/Metal/SIMD comparison | Existing local agent | Review committed evidence; do not absorb its dirty worktree. |
| Host WM/compiler bootstrap | Primary rendering agent | Do not race another bootstrap writer; host PASS precedes QEMU WM. |
| Final verification | Highest-capability primary reviewer | Review all sidecar findings and issue final PASS/FAIL. |

- Verify each acceptance criterion at most once per session.
- Stop after three fix/verify cycles for one feature and record the exact
  failure.
- Do not accept CPU mirrors, upload-only receipts, synthetic handles, static
  screenshots, or source checks as GPU proof.
- Do not claim the goal complete until every required lane has authoritative
  live PASS evidence.
