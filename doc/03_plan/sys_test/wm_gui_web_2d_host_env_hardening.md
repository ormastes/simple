# WM/GUI/Web/2D Host Environment Hardening Test Plan

## Test Layers

- `test/03_system/check/gui_showcase_perf_probe_exit_contract_spec.spl` proves
  a crash or timeout cannot be overwritten by complete-looking partial perf
  rows; its self-test is renderer-free and does not promote the 200 FPS row.

| Layer | Spec | Primary proof |
|---|---|---|
| Unit | `test/01_unit/lib/common/ui/host_env_contract_spec.spl` | Every capability/receipt validator branch |
| Component | `test/02_integration/os/hosted/hosted_web_content_session_spec.spl` | Real BrowserSession hit-test, DOM mutation, content update, exact rerender |
| System | `test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl` | Real Linux screen input through canonical frame/readback plus native host matrix |

<!-- sdn-diagram:id=wm_gui_web_2d_host_env_hardening.test_plan -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=wm_gui_web_2d_host_env_hardening.test_plan hash=sha256:auto render=ascii
@layout dag
@direction LR
UnitContract -> ComponentBridge
ComponentBridge -> LinuxLiveSystem
LinuxLiveSystem -> CoverageReport
LinuxLiveSystem -> PerformanceReport
LinuxLiveSystem -> RenderDocArtifact
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=wm_gui_web_2d_host_env_hardening.test_plan hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Manual-First System Flow

1. `Inspect the real host capabilities`
2. `Inject one screen-originated event`
3. `Follow the event through WM and GUI dispatch`
4. `Render the resulting canonical composition`
5. `Read back and compare the backend buffer`
6. `Capture the Vulkan frame with RenderDoc`
7. `Reject missing or duplicate retained 4K and 8K producer fields`
8. `Audit both retained workloads with the canonical aggregate validator`
9. `Admit current 4K and 8K timing RSS baseline and native-binary evidence`

The supporting structural scenario uses `Verify the retained contract binds a
forward Vulkan revision`; it cannot promote a host row.

## Requirement Coverage

| Requirement | Unit | Component | System |
|---|---:|---:|---:|
| REQ-001 | yes | — | yes |
| REQ-002–006 | validators | yes | yes |
| REQ-007 | classifier | native SIMD parity | host matrix |
| REQ-008 | validator | strict Vulkan | host matrix |
| REQ-009 | validator | capture/log/replay freshness | real `.rdc`/blocked |
| REQ-010–012 | yes | yes | manual/audits |

## Coverage and Performance

Run the existing Simple coverage engine for the owned contract/bridge modules;
require 100% classifier/validator branches and at least 98% overall. Performance
is a separate bounded run: 12 warm-up plus at least 20 samples, median/p95/max
RSS, exact output first, compared only to the matching retained device bucket.
Coverage evidence must contain stable decision rows with both true and false
counts; line/function-only output cannot satisfy the branch threshold.
Compiler inventory tests also require untouched zero/zero sites, branchless
header-only manifests, generated-CFG exclusion, authored wrapper paths, and
matching runtime counts through the Stage4 LLVM/core-C route.

## External Host Rows

| Row | Owner | Native prerequisite | Retained artifact | Resume command | Status rule |
|---|---|---|---|---|---|
| ARM NEON | `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | Prepared aarch64 host with NEON and an admitted pure-Simple CLI | `build/cpu-simd-engine2d-arch-matrix/aarch64/out/evidence.env` | `CPU_SIMD_ARCH_MATRIX_AARCH64_SIMPLE_BIN=bin/simple sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | blocked until native |
| RISC-V RVV | `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | Prepared riscv64 host with RVV and an admitted pure-Simple CLI | `build/cpu-simd-engine2d-arch-matrix/riscv64/out/evidence.env` | `CPU_SIMD_ARCH_MATRIX_RISCV64_SIMPLE_BIN=bin/simple sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | blocked until native |
| Vulkan/RenderDoc | Existing Vulkan/RenderDoc setup owners | Linux Vulkan host with `renderdoccmd` | `build/renderdoc/simple-gate/evidence.env` | `sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple` | valid `RDOC` required |
| Chrome/Electron | Existing browser-backing setup owner | Browser Vulkan backing | `build/gui-web-2d-vulkan-env-browser-backing/evidence.env` | `sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc` | browser Vulkan backing and ARGB parity required |
