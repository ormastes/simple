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
7. `Measure the retained rendering workload`

## Requirement Coverage

| Requirement | Unit | Component | System |
|---|---:|---:|---:|
| REQ-001 | yes | — | yes |
| REQ-002–006 | validators | yes | yes |
| REQ-007 | classifier | native SIMD parity | host matrix |
| REQ-008 | validator | strict Vulkan | host matrix |
| REQ-009 | validator | capture outcome | real `.rdc`/blocked |
| REQ-010–012 | yes | yes | manual/audits |

## Coverage and Performance

Run the existing Simple coverage engine for the owned contract/bridge modules;
require 100% classifier/validator branches and at least 98% overall. Performance
is a separate bounded run: 5 warm-up plus at least 20 samples, median/p95/max
RSS, exact output first, compared only to the matching retained device bucket.
Coverage evidence must contain stable decision rows with both true and false
counts; line/function-only output cannot satisfy the branch threshold.

## External Host Rows

| Row | Resume command | Status rule |
|---|---|---|
| ARM NEON | `bin/simple test test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl --mode=native` on prepared aarch64 | blocked until native |
| RISC-V RVV | same command on prepared riscv64 RVV | blocked until native |
| Vulkan/RenderDoc | `sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple` | valid `RDOC` required |
| Chrome/Electron | `sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc` | browser Vulkan backing and ARGB parity required |
