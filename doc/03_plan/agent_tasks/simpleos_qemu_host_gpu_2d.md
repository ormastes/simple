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
- Processing performance receipt: `HOST_GPU_PROCESS_PERF`; checker: `processing_perf_evidence_valid`; manual step: `Classify device processing preference`; fail-fast placeholder: `fail("ProcessingIR preference evidence missing")`
- Exact fixture constants: `HOST_GPU_FIXTURE_*`; oracle: `host_gpu_fixture_expected_pixel`; checker: `serial_render_fixture_valid`; manual step: `Render the selected 1280x720 canonical fixture`; fail-fast placeholder: `fail("1280x720 host-GPU fixture evidence missing")`

## Lanes

| Lane | Owner | Deliverable |
|---|---|---|
| protocol codec/validation | Codex Spark | bounded Pure Simple records and malformed-input tests |
| x86_64 Linux Vulkan slice | Codex Spark | live guest/daemon render and processing receipt |
| AArch64/RISC-V adapters | Codex Spark | canonical AArch64 and dynamic-scanout RV64 production sources plus fail-closed evidence contracts |
| host backend review | lower-model sidecar | Metal/DirectX/CUDA/Vulkan capability classification |
| canonical WM command trace | Codex Spark | required RECT/TEXT/IMAGE/embedding subset and exclusions |
| checked Vulkan provenance trace | Codex Spark | shared tri-state dispatch owner and raw CLEAR/RECT test boundary |
| native Metal Draw IR source | Codex Spark | shared-session surface, checked opacity composite, strict host admission |
| native Metal ProcessingIR source | Codex Spark | dedicated checked FillU32 kernel, pointer readback, strict daemon probe |
| QEMU/daemon RSS evidence | Codex Spark | concurrent component/combined sampling and isolated metrics self-test |
| ProcessingIR preference evidence | Codex Spark sidecars | independent CPU/device timing, correlated receipt, and fail-closed 1.5x classification |
| exact 1280x720 Draw IR fixture | Codex Spark sidecars | wire/memory audit, positional oracle, cached evidence exclusions, and manual review |
| compiler candidate admission | compiler/tooling owner | runner `_run_candidate_admission_pinned` owns exact `p2_add` and invalid-mode admission; `_run_candidate_pinned` owns the authoritative guest build identity |
| pure-Simple SSpec execution | compiler/test-runner owner (TODO 572) | result-bearing no-seed single-spec path; separate from host-GPU admission |
| merge and generated-manual review | primary `/root` | wrapper/parser/manual accepted; native non-Linux rows remain open |
| final review | normal/highest-capability Codex | requirements, exclusions, security, NFR, manual quality |

Sidecars may not add raw `rt_*` aliases, architecture-specific public APIs,
fixture bypasses, synthetic handles, or passing placeholders.

## Current Handoff

- Wrapper and fail-closed self-test: implemented.
- Shell `candidate_frontend_smoke` and `simple_binary_is_valid` now live in
  `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`, sourced
  by both bootstrap and the QEMU wrapper. `_QemuRunner`
  `_candidate_frontend_smoke` keeps the equivalent pure-Simple contract. The
  wrapper self-test and shared-shell syntax check pass; runner execution remains unproved until a current
  pure-Simple CLI is available.
  Runner admission routes both `p2_add` and invalid-mode probes through
  `_run_candidate_admission_pinned`. Its exact contract uses a private
  temporary cache/output/log; self-pins
  `SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`, and
  `SIMPLE_FRONTEND_DELEGATE` to the candidate; neutralizes inherited
  execution/worker/bootstrap selection with `SIMPLE_EXECUTION_MODE=''`,
  `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`, and `SIMPLE_BOOTSTRAP=0`; forbids stub
  fallback; and builds the checked-in `p2_add.spl` with
  Cranelift/core-C-bootstrap/entry-closure/one-binary under 60 seconds, executes
  it under 5 seconds, and requires exact stdout `5`. The old
  whole-tree `check startup_simple.spl` result is invalid because it always appends global
  repository hygiene and Git subguards that are not authoritative in a
  jj-only workspace without `.git`; bootstrap retains only its focused
  `check src/app/cli/bootstrap_main.spl`. After admission, `build_os_with_backend`
  applies `_apply_build_env` and routes the real guest native-build through
  `_run_candidate_pinned`, preserving target settings while pinning compiler
  identity. The build therefore cannot re-enter a sibling or seed delegate.
  Shared CLI symlink resolution makes authoritative worker delegation safe for
  candidates such as `bin/simple`; the focused
  `test/01_unit/app/io/cli_argv0_resolution_spec.spl` contract adds no `rt_*` alias.
  Source presence is not a PASS.
- All five split `_QemuRunner` modules now use shared I/O/process/time owners;
  `runner_targets` also replaces shell `cat` with `file_read`. TODO 573 stays
  open only for native child-scoped environment, platform-neutral temporary
  directories, and cross-platform safe timeout execution.
- TODO 573 implementation order is provider-complete timeout/capture, Unix
  process-group plus Windows Job Object cleanup, child-env overlay, atomic host
  temp creation, then runner `env`/`mktemp` removal. The Rust SFFI timeout alone
  is insufficient because core-C lacks it and its timeout child lacks group setup.
- TODO 574's overflow-safe Windows monotonic conversion is implemented in
  `src/runtime/runtime_time.c` and `src/runtime/platform/platform_win.h` by
  dividing QPC ticks before scaling remainders. The later split of elapsed
  timing from wall-clock artifact names remains open; this slice preserves
  `_now_ms`.
- The existing foreign-parser/Stage-4 recovery lane remains under
  `doc/08_tracking/bug/native_build_stage4_pre_object_spin_2026-07-13.md`; this
  admission work does not duplicate it.
- Pure-Simple focused SSpec execution remains unavailable and is not part of
  the admission patch. TODO 572 owns replacing `rt_cli_run_tests` and the Rust
  `rt_cli_run_file` interpreter with a result-bearing pure-Simple runner path.
- Retained cached Linux/Vulkan evidence contains exact x86_64, AArch64, and
  RV64 render and ProcessingIR receipts; it is not fresh production evidence.
- Fresh pure-Simple guest builds and all live QEMU rows remain blocked by TODO
  548's compiler/runtime deployment work. No current live PASS is claimed.
- x86_64 production and the new AArch64 boot-owned RAMFB entry wire canonical
  `DesktopShell` frames through `Engine2dWmFrameExecutor`. AArch64
  source/build-scenario wiring and correlated production-wrapper source/self-test
  coverage are present. Its fw_cfg DMA and PL011 input now pass through
  architecture-owned facades instead of the legacy `wm_entry_io.spl` closure,
  but real process ownership and
  fresh compile/QEMU evidence remain open under TODO 565/TODO 548. RISC-V now
  uses an architecture display facade, dynamic VirtIO mode discovery, and a
  contract-v2 canonical-desktop gate. Its source-ready UART loop reuses the
  existing nonblocking 16550 owner and shared `WmAction` mapper, rerenders only
  changed compositor state through `Engine2dWmFrameExecutor`, and requires a
  checked VirtIO-GPU present for each changed frame. WFI is intentionally
  excluded because UART interrupts are disabled (`IER=0`); root/higher review
  also placed `serial_init` after module initialization. TODO 567 retains the
  pure-Simple DMA transport migration rather than treating the historical
  fixed-anchor probe as production evidence. TODO 565 and TODO 548 remain open
  for compiled/live proof; this source contract is not a QEMU or GPU PASS.
- NFR-006 remains open under TODO 566: the source-ready probe and production
  owners now retain one boot-monotonic device-init-to-decision interval, ordered
  Metal/DirectX/Vulkan attempts, and final selection/fallback; daemon HELLO time
  is supporting per-attempt evidence only. The local parser/self-test lane and
  current Linux native row remain active; only unavailable Windows/macOS native
  timing rows are postponed. Applicability comes from the retained executed
  `-accel` token plus matching host ISA, not ISA equality; AArch64, RV64, and
  same-ISA TCG validate ordering, counting, boundaries, and fail-closed behavior
  but cannot close native latency. Valid equal clock samples use a 1 us floor.
- NFR-003 source, parser, and self-test evidence now carries exactly 20 warm
  1280x720 render/readback samples after the full positional oracle, validates
  consecutive generations and stable run/backend/device/checksum provenance,
  and computes nearest-rank p95 with the 16,700 us native limit. Native
  applicability is bound to the row's exact retained QEMU argv marker and a
  matching KVM/HVF/WHPX host/ISA; TCG remains correctness-only. NFR-005 evidence
  carries concurrently sampled daemon, QEMU, and combined maxima across both
  AArch64 boots. TODO 563 remains open until fresh current-host native and TCG
  rows exercise the contract and a native row proves both the p95 and 256 MiB
  targets. If the 20 extra samples expose a real timeout, the operator may set
  `SIMPLEOS_HOST_GPU_QEMU_TIMEOUT` for that run; the default remains unchanged.
  NFR-001's exact
  1280x720 fixture and NFR-004's 1.5x preference decision are tracked separately
  by TODO 569 and TODO 570 instead of being inferred from 64x48 parity. The
  daemon and cached-report checker now implement the correlated classification
  contract, but TODO 570 stays open until prepared native rows execute it.
  TODO 569's source contract now adds the selected 1280x720 positional oracle
  without replacing the smaller IMAGE regression; it also stays open for fresh
  supported-host execution.
- Final reviewer: primary `/root`; native Metal implementation is present but
  its done mark, DirectX, and remaining CUDA receipts remain rejected without
  prepared-host evidence.
- Checked raw framebuffer dispatch: traced by Spark and accepted by the
  independent normal/highest-capability reviewer. Production WM host execution
  now uses device-rendered shared-session offscreen surfaces and checked
  opacity. Production x86 guest submission now maps BAR2 into the active VMM,
  derives request generations from the idle wire slot, validates device receipts,
  and presents checked readback with local fallback. Fresh QEMU/p95 evidence and
  TODO 552's selected 4K capacity change remain open. The production transcript
  now emits one scoped `HOST_GPU_MAP_OK` before its first negotiation event and
  rejects missing or late mapping evidence. The
  reusable checked IMAGE src-over primitive and full-target opacity-1000
  RECT/IMAGE admission plus preflighted canonical TEXT glyph compositing are
  implemented. Smaller/offscreen device surfaces and opacity are covered by the
  canonical WM integration boundary.
