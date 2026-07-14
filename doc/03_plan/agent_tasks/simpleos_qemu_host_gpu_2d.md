<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Agent Tasks

## Shared Names Defined Before Sidecars

- Capsule: `SimpleOsHostGpuSession`
- Records: `SimpleOsHostGpuHello`, `SimpleOsHostGpuRequest`, `SimpleOsHostGpuReceipt`
- Wrapper: `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`
- Manual steps: `Probe the QEMU guest GPU capability`; `Render and read back the Simple 2D parity fixture`; `Run the ProcessingIR parity fixture`; `Report device-backed host acceleration evidence`
- Setup/checkers: `simpleos_host_gpu_prepare_row`, `simpleos_host_gpu_validate_receipt`, `simpleos_host_gpu_compare_oracles`
- Placeholder: `fail("SimpleOS QEMU host-GPU protocol not implemented")`
- Checked dispatch: `vulkan_dispatch_framebuffer_compute_checked`; backend mapper: `_dispatch_framebuffer_checked`
- Checked IMAGE dispatch: `vulkan_dispatch_image_composite_checked`; manual step: `Render one clipped alpha IMAGE through Vulkan src-over`
- Checked-raw manual steps: `Dispatch the raw CLEAR and solid RECT fixture through checked Vulkan commands`; `Reject unchecked or fallback raw rendering before device-backed receipt`
- Checked-raw checkers: `submit_checked_clear_rect`; `expect_device_backed_clear_rect_readback`
- Production guest helpers: `map_qemu_host_gpu_ivshmem_bar2_active_vmm`; `host_gpu_ivshmem_next_generation`; `Engine2dWmFrameExecutor._render_host_gpu`
- Production manual step: `Select host presentation or the existing local production renderer`
- Metal owner interfaces: `MetalBackend.init_with_session`; `MetalBackend.draw_image_blend_checked`; `Engine2D.create_shared_metal_offscreen`; `Engine2D.draw_metal_image_blend_checked`

## Lanes

| Lane | Owner | Deliverable |
|---|---|---|
| protocol codec/validation | Codex Spark | bounded Pure Simple records and malformed-input tests |
| x86_64 Linux Vulkan slice | Codex Spark | live guest/daemon render and processing receipt |
| AArch64/RISC-V adapters | Codex Spark | AArch64 production source plus correlated wrapper source/self-test; RISC-V probe remains |
| host backend review | lower-model sidecar | Metal/DirectX/CUDA/Vulkan capability classification |
| canonical WM command trace | Codex Spark | required RECT/TEXT/IMAGE/embedding subset and exclusions |
| checked Vulkan provenance trace | Codex Spark | shared tri-state dispatch owner and raw CLEAR/RECT test boundary |
| native Metal Draw IR source | Codex Spark | shared-session surface, checked opacity composite, strict host admission |
| native Metal ProcessingIR source | Codex Spark | dedicated checked FillU32 kernel, pointer readback, strict daemon probe |
| QEMU/daemon RSS evidence | Codex Spark | concurrent component/combined sampling and isolated metrics self-test |
| merge and generated-manual review | primary `/root` | wrapper/parser/manual accepted; native non-Linux rows remain open |
| final review | normal/highest-capability Codex | requirements, exclusions, security, NFR, manual quality |

Sidecars may not add raw `rt_*` aliases, architecture-specific public APIs,
fixture bypasses, synthetic handles, or passing placeholders.

## Current Handoff

- Wrapper and fail-closed self-test: implemented.
- Retained cached Linux/Vulkan evidence contains exact x86_64, AArch64, and
  RV64 render and ProcessingIR receipts; it is not fresh production evidence.
- Fresh pure-Simple guest builds and all live QEMU rows remain blocked by TODO
  548's compiler/runtime deployment work. No current live PASS is claimed.
- x86_64 production and the new AArch64 boot-owned RAMFB entry wire canonical
  `DesktopShell` frames through `Engine2dWmFrameExecutor`. AArch64
  source/build-scenario wiring and correlated production-wrapper source/self-test
  coverage are present, but real process ownership and
  fresh compile/QEMU evidence remain open under TODO 565/TODO 548;
  RISC-V remains a protocol/scanout probe pending TODO 567.
- NFR-006 remains open under TODO 566: receipt timing covers daemon HELLO work,
  not guest-observed device initialization plus all fallback attempts.
- NFR-005 evidence now carries concurrently sampled daemon, QEMU, and combined
  maxima across both AArch64 boots; TODO 563 remains open until fresh live rows
  prove the 256 MiB target and warm multi-sample latency p95. NFR-001's exact
  1280x720 fixture and NFR-004's 1.5x preference decision are tracked separately
  by TODO 569 and TODO 570 instead of being inferred from 64x48 parity.
- Final reviewer: primary `/root`; native Metal implementation is present but
  its done mark, DirectX, and remaining CUDA receipts remain rejected without
  prepared-host evidence.
- Checked raw framebuffer dispatch: traced by Spark and accepted by the
  independent normal/highest-capability reviewer. Production WM host execution
  now uses device-rendered shared-session offscreen surfaces and checked
  opacity. Production x86 guest submission now maps BAR2 into the active VMM,
  derives request generations from the idle wire slot, validates device receipts,
  and presents checked readback with local fallback. Fresh QEMU/p95 evidence and
  TODO 552's selected 4K capacity change remain open. The
  reusable checked IMAGE src-over primitive and full-target opacity-1000
  RECT/IMAGE admission plus preflighted canonical TEXT glyph compositing are
  implemented. Smaller/offscreen device surfaces and opacity are covered by the
  canonical WM integration boundary.
