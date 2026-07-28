# TODO317 — WM/GUI/Web/2D cross-host acceptance evidence

- Filed: 2026-07-28
- Priority: P1
- Status: open; every row is fail-closed
- Ledger: `doc/08_tracking/todo/todo_db.sdn` ID 312
- Stable handoff: `doc/08_tracking/todo/simple_renderdoc_external_host_postponed_2026-07-27.md`
- Merge owner: WM/GUI/Web/2D host-environment acceptance owner
- Final reviewer: independent highest-capability reviewer

## Authority and non-duplication

TODO317 is the single acceptance umbrella for the deferred host evidence. It
replaces absent ledger IDs 580, 583, 585, and 589 where current documents used
those IDs for source-matched runtime, optional Electron, or admitted coverage
proof. It does not reopen or duplicate their old database rows.

Implementation-specific work stays with its existing owner. In particular,
the historical 4K/8K baseline policy remains in
`doc/08_tracking/todo/rendering_performance_historical_regression_baseline_2026-07-27.md`;
SimpleOS transports and board adapters remain in
`doc/08_tracking/todo/simpleos_qemu_host_gpu_postponed_2026-07-15.md` and
`doc/08_tracking/feature/simpleos_cross_host_board_gpu_requests_2026-07-26.md`;
and detailed RenderDoc handoff state remains in the stable ledger above.
TODO317 admits their completed evidence together; it does not replace their
implementation scopes.

Local implementation lanes A/B/C remain with their existing owners and are
not deferrals under TODO317: (A) the strict RenderDoc
producer/replay/classifier identity join, (B) target-owned
x86_64/AArch64/RV64 per-operation SIMD producers feeding the BRR1 host join,
and (C) detailed command/pipeline/shader/resource/transition snapshots.
Compiler, backend, producer/parser, or wrapper defects found locally must be
fixed or tracked by those owners before handoff. This matrix consumes their
green outputs without absorbing or postponing the implementation work.

Only backend/native/live execution that genuinely requires a prepared external
environment is deferred here: native ISA hosts, real display/GPU/RenderDoc and
browser hosts, platform/QEMU/board runs, and the qualified performance host.
Pure-Simple CLI admission, repo-native counterpart logic, contract/docgen work,
and locally reproducible backend defects remain local prerequisite lanes.

## Common admission contract

Every row must use the same clean source revision and an admitted, source-matched
pure-Simple CLI. Rust seed, repo launcher, translated/emulated native-host
claims, mutable provider inputs, fixture overrides, CPU mirrors, screenshots,
and cached or fallback pixels cannot promote a row.

Retain `build/host-env-acceptance/<row>/manifest.env` and its SHA-256 with:

- source revision, clean-state result, source-manifest SHA-256, command and
  allow-listed environment;
- CLI path, version, runtime kind, executable SHA-256, compiler/provider/library
  hashes, target triple, OS/kernel, CPU/ISA, device/driver/ICD identity;
- evidence env, stdout/stderr, build/run logs, captures, replay/readback files,
  and SHA-256 for every referenced regular no-follow artifact;
- one event/frame/composition identity, ordered focus/pointer/key/text/click
  receipts, backend selection, positive handle, submit/fence/completion,
  device-origin readback geometry/format/hash, and zero oracle mismatches;
- warm-up/sample counts, p50/p95/FPS/max RSS, immutable baseline path/hash and
  environment bucket for 4K/8K rows; and
- owner, capture time, host identity, reviewer decision, and typed first blocker.

Changing any retained artifact after capture invalidates the row. Credentials
remain outside manifests, commands, logs, and repository evidence.

The Linux X11/display-input and framebuffer-readback rows also remain blocked
while `GLYPH_RGB_SHA256=pending` in the canonical live-window wrapper. A
prepared real X11/Vulkan host must capture the glyph crop, obtain independent
review, pin its lowercase SHA-256, and rerun the wrapper. A fixture, synthetic
crop, screenshot-only result, or locally guessed hash cannot calibrate it.
The calibration capture command is
`LINUX_HOSTED_WM_CALIBRATE_GLYPH=1 SIMPLE_BIN=<admitted-simple> scripts/check/check-linux-hosted-wm-live-window-evidence.shs`;
its calibration-only failure is reviewed and pinned before the normal command
may produce acceptance evidence.

## Required rows and exact resume commands

Commands are handoffs, not claims that a row has run. Replace angle-bracket
placeholders with an already admitted artifact; record the resolved value in
the immutable manifest.

| Row | Owner | Prerequisites | Exact resume command | Acceptance evidence |
|---|---|---|---|---|
| Pure-Simple CLI and coverage identity | bootstrap/runtime owner | clean source; no-stub source-matched Stage 4 CLI; docgen/test runner and compiler decision manifest | `SIMPLE_BIN=<admitted-simple> sh scripts/check/check-bootstrap-essential-tools-smoke.shs` | CLI/source/provider hashes, no-stub admission, unit/component/system results, zero-stub manuals, compiler-emitted zero-count denominator and admitted 98–100% owned-lane coverage report |
| Native x86 SIMD | prepared x86_64 host operator | admitted CLI; x86_64 host with SSE4.2 or AVX2 | `CPU_SIMD_ARCH_MATRIX_X86_64_SIMPLE_BIN=<admitted-simple> sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | `native_host`, executed feature/hits, exact scalar fill/copy/alpha/scroll/frame parity, compiler/source/receipt hashes |
| Native ARM NEON | prepared AArch64 host operator | admitted AArch64 CLI and NEON host | `CPU_SIMD_ARCH_MATRIX_AARCH64_SIMPLE_BIN=<admitted-simple> sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | native NEON hits and the same immutable scalar-oracle receipt; QEMU does not promote this row |
| Native RISC-V RVV | prepared riscv64 host operator | admitted riscv64 CLI and RVV-capable host/toolchain | `CPU_SIMD_ARCH_MATRIX_RISCV64_SIMPLE_BIN=<admitted-simple> sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | native RVV hits and the same immutable scalar-oracle receipt; QEMU does not promote this row |
| Linux X11/winit vertical slice | Linux hosted-WM owner | admitted CLI, real X11 display, winit window and screen-originated input tool; reviewed glyph calibration with `GLYPH_RGB_SHA256` no longer `pending` | `SIMPLE_BIN=<admitted-simple> scripts/check/check-linux-hosted-wm-live-window-evidence.shs` | ordered screen-to-WM-to-Web mutation and same-frame `DrawIrComposition`/Engine2D device receipt, reviewed glyph crop/hash, before/after captures and hashes |
| Linux Vulkan/device readback | prepared Linux Vulkan owner | admitted CLI, Vulkan ICD/driver/device and browser backing | `SIMPLE_BIN=<admitted-simple> GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing && SIMPLE_BIN=<admitted-simple> GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-run-current scripts/setup/setup-gui-web-2d-vulkan-env.shs --run` | validated module, selected device/driver, queue submit/fence, positive handle, device-origin ARGB readback and exact CPU-SIMD parity |
| External RenderDoc on Simple Vulkan | Simple Vulkan capture owner | passing Vulkan row and external RenderDoc runtime/API | `SIMPLE_BIN=<admitted-simple> scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple` | capture/replay logs, regular `.rdc` with `RDOC` magic, Simple device readback, all artifact hashes, strict Simple gate PASS |
| Repo-native Simple RenderDoc counterpart | Simple 2D RenderDoc Backend Equivalence owner | admitted CLI plus required focused/qualification corpus inputs | `SIMPLE_BIN=<admitted-simple> sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --profile=qualification` | deterministic records/diffs, backend equivalence, QEMU/board receipts where required, pure-Simple capture inspection and aggregate PASS; this is not the external capture wrapper |
| Chrome external-host RenderDoc | prepared Chrome/RenderDoc owner | external RenderDoc, Chrome with Vulkan GPU process and valid HTML/CSS producer | `RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs` | Chrome GPU-process `.rdc`, GPU/Vulkan identity, HTML/CSS source hash, logs and replay/readback hashes |
| Electron/Chrome/Simple parity | browser-parity owner | pinned Electron install, Vulkan-backed Chrome/Electron, passing Simple Vulkan row | `SIMPLE_BIN=<admitted-simple> scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc` | three equal-dimension ARGB files and hashes, three zero-mismatch diffs, browser-backing identity, ordered interaction receipts and valid captures; Electron is corroborating, not a substitute for the pure-Simple row |
| Retained 4K and 8K performance | rendering-performance owner | admitted release CLI, GUI/perf host and approved immutable matching baselines | `RESOLUTION=4k SIMPLE_BIN=<admitted-simple> sh scripts/check/check-widget-showcase-4k-200fps.shs && RESOLUTION=8k SIMPLE_BIN=<admitted-simple> sh scripts/check/check-widget-showcase-4k-200fps.shs` | native executable hash, retained frame/readback proof, at least 200 FPS, p95 budget, RSS, p50/p95 deltas and +10% frame/+5% RSS historical limits for both rows |
| FreeBSD bootstrap/QEMU | FreeBSD bootstrap owner | QEMU, cloud image/network/SSH and admitted source inputs | `sh scripts/check/check-freebsd-bootstrap-qemu.shs --full` | pristine overlay/base hashes, guest identity, synchronized source hash, toolchain/bootstrap logs and resulting native artifact hashes; this is platform readiness, not native GPU proof |
| SimpleOS x86_64 QEMU | `/root/x86_qemu_owner` | admitted kernel/disk/manifest, QEMU x86_64 and firmware | `BUILD_DIR=build/simpleos_wm_fullscreen_evidence SIMPLE_BIN=<admitted-simple> sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | frozen manifest, kernel/disk hashes, serial/QMP/`pmemsave`, SSE parity, ordered input/frame/damage and timing/RSS |
| SimpleOS ARM64 QEMU | `/root/arm_qemu_owner` | admitted ARM64 ELF/FAT/manifest, QEMU AArch64 and firmware | `SIMPLE_BIN=<admitted-simple> sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs && SIMPLE_BIN=<admitted-simple> sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` | ELF/FAT hashes, serial/QMP/RAMFB, VirtIO/NEON guest receipts, frame/damage and timing/RSS; not native-host NEON promotion |
| SimpleOS RV64 QEMU | prepared RV64 host operator | admitted RV64 ELF, QEMU/QMP and PCI VirtIO input | `<admitted-simple> os build --scenario=riscv64-display-smoke && SIMPLE_BIN=<admitted-simple> scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input` | frozen manifest/ELF hash, serial/QMP/RAMFB, PCI/ISR/input/RVV guest receipt, parity and timing/RSS; not native-host RVV promotion |
| macOS Metal/Vulkan parity | prepared macOS owner | admitted macOS CLI, native Metal device and prepared Vulkan provider where available | `SIMPLE_BIN=<admitted-simple> sh scripts/check/check-macos-metal-2d-live-evidence.shs && SIMPLE_BIN=<admitted-simple> sh scripts/check/check-macos-vulkan-metal-2d-parity-evidence.shs <vulkan-evidence.env> <metal-evidence.env> build/host-env-acceptance/macos/parity.env` | native window/events, Metal submit/completion/device readback, provider/device hashes, same-scene CPU/NEON parity; Vulkan absence remains typed and cannot fabricate parity |
| Windows Vulkan/DirectX | prepared Windows owner | admitted `simple.exe`, Vulkan and D3D12 drivers plus GPU capture tools | `pwsh -File scripts/check/check-windows-gui-web-2d-evidence-bundle.ps1 -RequireFullCompletion` | Vulkan/DirectX/D3D12 device/readback/capture rows, executable/provider/driver hashes, native events, exact CPU-SIMD parity and full bundle PASS |

## Aggregate acceptance

After every applicable row is fresh, run:

```sh
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
<admitted-simple> run src/app/test/test_host_env.spl -- --format=json
```

TODO317 closes only when every required row is `pass`, every platform-unavailable
row is explicitly reviewed as not applicable rather than silently omitted, all
artifact hashes revalidate, the architecture/design/plan/guide and generated
manuals name the same commands, and an independent reviewer signs the aggregate.
Any `blocked`, `fail`, stale, duplicate, malformed, fixture, fallback, or
unhashed artifact keeps TODO317 open.
Local A/B/C are prerequisites, not TODO317 rows; TODO317 cannot close while any
of them is absent even if every available native/live host row has evidence.

## Dependency links

- Requirements: `doc/02_requirements/feature/wm_gui_web_2d_host_env_hardening.md`
- Architecture: `doc/04_architecture/wm_gui_web_2d_host_env_hardening.md`
- Design: `doc/05_design/wm_gui_web_2d_host_env_hardening.md`
- Test plan: `doc/03_plan/sys_test/wm_gui_web_2d_host_env_hardening.md`
- Agent plan: `doc/03_plan/agent_tasks/wm_gui_web_2d_host_env_hardening.md`
- Operator guide: `doc/07_guide/app/ui/test_host_env.md`
- System spec/manual: `test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl`, `doc/06_spec/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.md`
- RenderDoc handoff: `doc/08_tracking/todo/simple_renderdoc_external_host_postponed_2026-07-27.md`
- SimpleOS/QEMU handoff: `doc/08_tracking/todo/simpleos_qemu_host_gpu_postponed_2026-07-15.md`
- Historical performance policy: `doc/08_tracking/todo/rendering_performance_historical_regression_baseline_2026-07-27.md`
