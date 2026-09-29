# Render-performance campaign resume matrix — 2026-08-12

This is the authoritative current-state companion to
[`render_perf_redesign_plan_2026-08-06.md`](render_perf_redesign_plan_2026-08-06.md).
It reconciles the later implementation and evidence without rewriting the
historical plan or reports.  `PASS` below means only the named narrow gate;
**no row below is an overall 8K/80 admission unless it has a completed receipt
accepted by `scripts/check/check-render-8k80-receipt.shs`.**

## Admission boundary

The current compiler/runtime authority has **Cycle 7 Stage 2 admitted only**
at `/mnt/data/.simple/bootstrap/fv2-context-authority-20260812/cycle7`.
Its clean frozen source worktree exists, but its pinned Stage-3 resume wrapper
predates the provenance repairs; there is no provenance-admitted Stage 3,
Stage 4, or deployment. Consequently the admitted Stage-2 output cannot
authorize native Vulkan, native Simple-frame, or booted-SimpleOS performance
execution.

Canonical blocker and retained state:

- [`self_hosted_runtime_authority_republish_path_2026-08-12.md`](../../../08_tracking/bug/self_hosted_runtime_authority_republish_path_2026-08-12.md)
- [`vulkan_engine2d_native_jit_missing_rt_struct_receiver_valid_2026-08-12.md`](../../../08_tracking/bug/vulkan_engine2d_native_jit_missing_rt_struct_receiver_valid_2026-08-12.md)
- The Cycle 7 admitted Stage-2 output and transcript are evidence only; no
  Stage-3/4 or deploy artifact is retained as current authority. Do not treat
  older sibling-root artifacts as this lineage.

Resume only after the compiler owner creates a **fresh frozen source worktree**
whose source identity is recorded against the admitted Stage-2 receipt, reruns
and admits Stage 2 from that worktree, and establishes a stable compiled-root
snapshot/released authority lock.  Stage 3 is forbidden until those two
fresh-worktree/Stage-2 gates pass; Stage 4 and deployment remain forbidden
until Stage 3 is admitted.  Then follow the commands below exactly; stop at
the first failed gate:

```sh
# 1. Read-only confirmation that the selected authority carries the repair.
nm -g --defined-only <authority>/libsimple_runtime.a | \
  rg 'rt_struct_receiver_valid'

# 2. One provenance-owning Stage-4 deploy from the stable snapshot.
timeout -k 30s 3600s sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --mode=dynload --deploy \
  --output=build/bootstrap-render-authority-20260812 \
  --progress --progress-interval=30

# 3. Admit the deployed candidate once; it rejects seeds and stale artifacts.
sh scripts/check/check-deployed-binary-capabilities.shs

# 4. Only after admission PASS, collect the native Vulkan gate once.
env SIMPLE_VULKAN_READBACK_TIMEOUT_SECS=75 \
  SIMPLE_VULKAN_READBACK_WORK_DIR=build/vulkan-engine2d-readback-live-20260812 \
  REPORT_PATH=doc/09_report/vulkan_engine2d_readback_2026-08-12.md \
  sh scripts/check/check-vulkan-engine2d-readback.shs
```

The first command is a repair-presence check, not admission.  A linked but
withheld Stage 4, a Rust seed, a raw source command, or a stale binary is a
blocked result, never a fallback.

Current live observation (2026-08-12): Cycle 7 Stage 2 is admitted at
`/mnt/data/.simple/bootstrap/fv2-context-authority-20260812/cycle7`, but there
is no Stage-3/4 artifact or deployment. The next owner must create a fresh
frozen worktree containing the receiver-allocation repair, then re-admit Stage
2 with a provenance-safe resume wrapper before attempting Stage 3; no older
campaign or sibling-root artifact may satisfy this prerequisite.

The prior `cycle6` diagnostic from the clean frozen worktree at
`/mnt/data/.simple/bootstrap/fv2-context-authority-20260812/worktree` rejected
its Stage-2 runtime: both sanity probes exited 132 (`runtime error: invalid
field receiver`). Its exact candidate was not retained, so that result remains
non-reproducible diagnostic evidence only. The same frozen worktree's bounded
`cycle7` now has a new `stage2-sanity.env` with `status=pass`, a stable candidate
SHA, and `runtime-admitted.txt`. This admits **only Cycle 7 Stage 2**. Its source
worktree is still clean, but the pinned resume wrapper predates the provenance
repairs: it overwrites the admitted source binding and uses unsafe lock cleanup.
The shared active source tree has 281 dirty compiler/app/lib paths and cannot
substitute for it. A quiescent worktree plus a provenance-safe wrapper whose
tool-authority binding matches Cycle 7 is required before Stage 3; Stage 3/4,
deployment, and all rendering gates remain forbidden.

## Current lane matrix

| Lane | Current verified state | Still required for its 8K/80 acceptance criterion | Resume command and retained artifact |
|---|---|---|---|
| CPU SIMD x86 / Arm / RISC-V | **PARTIAL.** x86 AVX2/SSE2, AArch64 NEON QEMU-user, and RV64GCV RVV QEMU-user exact fill/parity paths pass. x86 row-kernel evidence shows only constant-fill/copy projections within 12.5 ms; opaque-image and mixed-alpha full repaint miss it. | Admitted Simple-frame runs for each ISA; measured 7680x4320 p50/p95/RSS/framebuffer checksum and a declared damage class. QEMU is instruction-path correctness, not Arm/RISC-V device throughput. | After Stage 4, run `CPU_SIMD_ARCH_MATRIX_STRICT=1 CPU_SIMD_ARCH_MATRIX_SKIP_RUN=0 CPU_SIMD_ARCH_MATRIX_TARGET_BUILD=1 BUILD_DIR=build/cpu-simd-engine2d-arch-matrix-stage4 REPORT_PATH=doc/09_report/ui/perf/cpu_simd_engine2d_arch_matrix_stage4.md sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs`, supplying admitted target binaries through `CPU_SIMD_ARCH_MATRIX_{X86_64,AARCH64,RISCV64}_SIMPLE_BIN`. Retained: `build/cpu-simd-engine2d-arch-matrix-native-perf-final/`, [CPU route evidence](../../../09_report/ui/perf/cpu_simd_in_place_blend_vector_route_2026-08-12.md). |
| Bare / SimpleOS | **PARTIAL.** The x86 host-user, AArch64 QEMU-user, and RV64 QEMU-user exact-fill matrix passes. | Boot a admitted SimpleOS image, prove displayed output with scanout/QMP checksum, then record full-frame fill/copy/blend timing and RSS. The user-mode matrix does not boot an OS or show a display. | Reconfirm narrow kernel evidence once: `timeout 120 bash scripts/check/check-simpleos-gui-fill-qemu-user-matrix.shs`. After Stage 4, run `SIMPLE_BIN=<admitted-stage4-cli> BUILD_DIR=build/simpleos_wm_fullscreen_evidence-stage4 REPORT_PATH=doc/09_report/os/simpleos_wm_fullscreen_evidence_stage4.md sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`. Retained: [QEMU-user matrix](../../../09_report/os/simpleos_bare_qemu_gui_fill_matrix_evidence_2026-08-12.md), [no-verdict blocker](../../../08_tracking/bug/baremetal_image_perf_probe_no_verdict_2026-08-12.md). |
| Vulkan Engine2D | **PARTIAL.** Exact strided transfer, swapchain ownership/device-adoption, damage-chain, and retained revision mechanisms have focused/live llvmpipe correctness evidence. Normal direct presentation is now fail-closed: only an exact frame revision with a fresh fenced submission generation, buffer ownership, adapter identity, and valid damage can skip readback; every rejected attempt explicitly takes the existing pixel fallback. The external-Winit present row additionally requires a live X11 or Wayland display; this host currently exports neither `DISPLAY` nor `WAYLAND_DISPLAY`. llvmpipe/Xvfb 8K rows miss 12.5 ms. | One admitted native run on a physical adapter with real adapter identity, dynamic and retained 7680x4320 p50/p95/RSS, completion/fallback state, pixel-device-readback checksum, and a real external-window present receipt. | After Stage 4 on a host with an owned X11/Wayland display and selected physical ICD: `env SIMPLE_VULKAN_READBACK_TIMEOUT_SECS=75 SIMPLE_VULKAN_READBACK_WORK_DIR=build/vulkan-engine2d-readback-live-2026-08-12 REPORT_PATH=doc/09_report/vulkan_engine2d_readback_2026-08-12.md sh scripts/check/check-vulkan-engine2d-readback.shs`; then run `bin/simple run test/05_perf/graphics_2d/bench_vulkan_8k_retained_damage.spl --mode=jit`. Retained: [live strided/presenter evidence](../../../09_report/ui/perf/vulkan_strided_transfer_live_2026-08-11.md), [JIT ABI refresh](../../../09_report/ui/perf/vulkan_8k_retained_jit_abi_refresh_2026-08-12.md). |
| DrawIR CPU / Vulkan | **PARTIAL.** Damage plans route to Vulkan without the previous generic full device readback. The F4 direct-present route binds no-readback submission to a fresh fenced generation and exact compositor revision, consumes candidates one-shot, and preserves explicit capture/fallback readback. It has a focused structural contract but no admitted/live device receipt yet. | Measured CPU and physical-Vulkan 8K dynamic rows with source labels, exact transfer bytes, checksum, RSS, fallback/completion, and presentation receipt. | Run the Vulkan admission command above first, then `bin/simple run test/05_perf/graphics_2d/bench_draw_ir_tiled_occlusion_8k.spl --mode=jit`. Retained: [damage-present route](../../../09_report/ui/perf/draw_ir_vulkan_damage_present_route_2026-08-12.md), [DrawIR/device seam](../../../09_report/ui/perf/vulkan_strided_transfer_live_2026-08-11.md). |
| WebRenderer / canonical DrawIR | **PARTIAL.** Retained tile plans and exact frame-switch receipts pass focused contracts; changed LOCAL consumption has an unresolved bounded-run failure. No separate WebIR is introduced. | Fix/admit the LOCAL consumer execution, then produce CPU and Vulkan 200-frame 8K dynamic/retained receipts. | After Stage 4: `SIMPLE_BIN=<admitted-stage4-cli> WEB_DRAW_IR_SWITCH_WORK_DIR=build/web_draw_ir_8k_frame_switch-stage4 SIMPLE_TIMEOUT_SECONDS=180 sh scripts/check/check-web-draw-ir-8k-frame-switch.shs`. Retained: [Web producer evidence](../../../09_report/ui/perf/web_renderer_retained_damage_producer_evidence_2026-08-11.md), `test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl`. |
| GUI / canonical DrawIR | **PARTIAL.** Eight-entry/one-8K-frame bounded retained content cache, exact NONE reuse, and persistent-target reuse pass; GUI LOCAL integration timed out and 8K benchmark fell back to interpreter. No GuiIR is introduced. | Execute GUI LOCAL parity after authority admission; then measure CPU/Vulkan 8K dynamic and retained rows with RSS/checksum/present receipts. | After Stage 4: `SIMPLE_TIMEOUT_SECONDS=240 bin/simple run test/perf/graphics_2d/bench_damage_checksum_8k.spl --mode=jit`. Retained: [GUI evidence](../../../09_report/ui/perf/gui_retained_content_frame_evidence_2026-08-11.md), `test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_dynamic_damage_spec.spl`. |
| Hosted WM | **PARTIAL.** WM retained frame switching passes software parity; existing-window Vulkan ownership and submit-only route pass focused contracts. The complete host-compositor source checker timed out without a diagnostic. | Execute the pending WM integration contracts using an admitted CLI; measure 8K CPU and physical Vulkan rows; boot SimpleOS separately for actual scanout proof. | After Stage 4: `SIMPLE_TIMEOUT_SECONDS=180 bin/simple test test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl --mode=interpreter --no-session-daemon`, then use the SimpleOS command above. Retained: [WM retained evidence](../../../09_report/ui/perf/wm_retained_frame_switch_evidence_2026-08-11.md), [existing-window seam evidence](../../../09_report/ui/perf/vulkan_strided_transfer_live_2026-08-11.md). |

## Final matrix admission

When every lane has independently emitted one fresh normalized receipt, run:

```sh
sh scripts/check/check-render-8k80-matrix.shs <normalized-receipt-file>
```

It requires each CPU, bare, Engine2D, DrawIR, Web, GUI, and WM row at
`7680x4320`, p95 at or below `12500` microseconds, known completion, no
fallback, and a real presentation/readback checksum appropriate to that lane.
Do not fabricate missing rows, relabel them as skipped, or use llvmpipe/QEMU
correctness receipts as physical-device performance evidence.

## Production PaintChunk occlusion prerequisite

<!-- codex-design -->

`chunk_occlusion.spl` is a standalone conservative analysis helper, not a
production render switch.  It must remain disconnected from normal DrawIR
execution until the three prerequisites below are implemented together and
accepted as one change.  In particular, the current delta path selects and
replaces commands by array index; it cannot represent a removed chunk.  Culling
against that path could leave an old command in the retained composition or
change painter order.

### Required capability boundary

1. **Canonical full-frame lowerer.** The reusable full-frame lowerer and
   composition/transaction adapter now exist at
   `render_opt/paint_chunk_draw_ir_lowerer.spl`; they require producer-supplied
   stable IDs and lockstep `PaintChunkRects`, preserve source order, and derive
   complete upsert/remove transactions. The production Web/GUI PaintChunk route
   still needs one owner that invokes this adapter for every frame and owns the
   stable identities, device-space bounds, surface, clip/effect/transform
   state, and command order. Both a fresh build and retained replay must use
   that same owner; the standalone `PaintChunkRects` rasterizer is not a
   substitute.
   The Blink background-only producer now supplies a limited compatible row
   stream (`blink-bg:<node-id>:0`) beside its unchanged direct-pixel path.
   Transparent background rows remain explicit and carry no opaque proof.
   It is not yet a complete Web PaintArtifact producer: borders, shadows,
   glyphs, effects, and their layer ordering must join the same producer before
   a compositor caller or retained replay is enabled.
2. **Atomic retained delta semantics.** Replace positional patching with a
   stable-identity delta that contains `upsert` and `remove` (or an equivalent
   tombstone which is suppressed before execution).  Build the next retained
   composition off to the side, validate its revision and complete identity
   set, then publish it atomically.  A removed, hidden, reordered, or
   reparented chunk must leave no executable stale command.  Any malformed
   delta, duplicate identity, revision discontinuity, resource mismatch, or
   incomplete set must abandon the retained update and replay the canonical
   full frame.
3. **Producer-owned opaque proofs.** Web and GUI producers must attach an
   exact proof only when the *actual emitted primitive* is a fully opaque,
   axis-aligned rectangle on the same target surface after transform, clip,
   effect, alpha, and resource evaluation.  Unknown/translucent/filter/mask,
   non-rect, cross-surface, or unbounded geometry is `UNKNOWN`, never an
   inferred opaque rect.  `chunk_occlusion` may cull only with that proof and
   must fail open (retain all candidates) on workspace exhaustion or any
   incomplete proof.

### Invariants and acceptance evidence

- Fresh canonical lowering and retained lowering are command-order and
  framebuffer-checksum equivalent for unchanged, changed, inserted, removed,
  reordered, clipped, and resource-revision-changing chunk sequences.
- A removal is observed in the same published frame: a later transparent or
  deleted chunk cannot reveal its own prior pixels or leave an earlier
  occluded command suppressed incorrectly.
- Occlusion only suppresses a candidate whose entire clipped device-space
  coverage is proven covered by later commands on the same surface; output is
  byte-identical to no-cull execution for overlapping opaque rectangles,
  partial coverage, opacity loss, clip/effect changes, and surface changes.
- The production caller records candidate, culled, visible, proof-incomplete,
  and fail-open counters.  A zero/unknown proof or a failed delta transaction
  is a full-frame fallback, not a performance success.
- Focused executable specs must cover the cases above and a hosted
  Web/GUI-to-WM frame path; after authority admission, one CPU and one physical
  Vulkan dynamic 8K receipt must show the declared cull class, exact checksum,
  command counts, presentation completion, and fallback state.  Until then,
  `bench_draw_ir_tiled_occlusion_8k.spl` is not an occlusion admission.

### File ownership and implementation handoff

| Owner | Files / responsibility |
|---|---|
| Canonical chunk data and stable identity | `src/lib/blink/entity/paint_chunk.spl`; `src/lib/common/ui/render_opt/property_trees.spl` |
| Complete production PaintChunk-to-DrawIR lowerer | `src/lib/common/ui/render_opt/paint_chunk_draw_ir_lowerer.spl` is the reusable adapter; wire its sole producer/execution call site through `src/os/compositor/compositor_engine2d.spl` |
| Geometry and source-to-lowerer contract | `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl` (replace its standalone-only role only after the canonical lowerer exists) |
| Transactional retained updates | `src/lib/common/ui/render_opt/draw_ir_delta.spl` |
| Conservative cull algorithm and counters | `src/lib/common/ui/render_opt/chunk_occlusion.spl` |
| Web/GUI opaque-proof production | `src/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_damage_consumer.spl`; `src/lib/gc_async_mut/ui/gui_content_renderer.spl` |
| Focused regressions | `test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl`; `test/01_unit/lib/common/ui/render_opt/chunk_occlusion_spec.spl`, plus hosted compositor integration coverage |

The rendering owner defines the shared stable-id, delta-operation, and
proof-record names before parallel work begins; the compositor owner merges
the production call path; the rendering performance owner reviews the complete
checksum and physical-device evidence.  No existing DrawIR code is authorized
to enable occlusion before this handoff is complete.

## Ownership and review

- Compiler/runtime authority: compiler owner; final reviewer: release/verify
  owner.
- CPU, Vulkan, DrawIR, Web, GUI, and WM row owners: their respective rendering
  lanes; final reviewer: rendering performance owner.
- SimpleOS scanout: OS/WM owner; final reviewer: rendering performance owner.
- No sidecar merge is implied by this matrix; it only records handoff and
  evidence boundaries.
