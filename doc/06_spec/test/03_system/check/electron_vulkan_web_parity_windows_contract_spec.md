# Electron Vulkan Web Parity Windows Contract

> Locks the Windows GUI app hardening contract for `scripts/check/check-electron-vulkan-web-parity-windows.shs`. The wrapper is a Windows-only evidence gate for comparing a real Electron/Chromium Vulkan frame against the pure-Simple Engine2D Vulkan web renderer. Off Windows it must emit a typed skip, not ambiguous prose.

<!-- sdn-diagram:id=electron_vulkan_web_parity_windows_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_vulkan_web_parity_windows_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_vulkan_web_parity_windows_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_vulkan_web_parity_windows_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Vulkan Web Parity Windows Contract

Locks the Windows GUI app hardening contract for `scripts/check/check-electron-vulkan-web-parity-windows.shs`. The wrapper is a Windows-only evidence gate for comparing a real Electron/Chromium Vulkan frame against the pure-Simple Engine2D Vulkan web renderer. Off Windows it must emit a typed skip, not ambiguous prose.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md |
| Research | doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md |
| Source | `test/03_system/check/electron_vulkan_web_parity_windows_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Locks the Windows GUI app hardening contract for
`scripts/check/check-electron-vulkan-web-parity-windows.shs`. The wrapper is a
Windows-only evidence gate for comparing a real Electron/Chromium Vulkan frame
against the pure-Simple Engine2D Vulkan web renderer. Off Windows it must emit a
typed skip, not ambiguous prose.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md
**Design:** doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md

## Syntax

```sh
SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test \
  test/03_system/check/electron_vulkan_web_parity_windows_contract_spec.spl \
  --mode=interpreter --clean

OS=Windows_NT EVWP_WORK=build/windows-electron-vulkan-web-parity \
  sh scripts/check/check-electron-vulkan-web-parity-windows.shs
```

## Acceptance

- The wrapper rejects Rust seed `simple` binaries.
- Non-Windows hosts emit `status=skip` and `reason=requires-windows`.
- Windows dependency skips use stable `status/reason` fields.
- Windows execution forces `SIMPLE_EXECUTION_MODE=interpret` for the
  pure-Simple app path.
- The compare step fails closed when the Simple-rendered JSON does not report
  `backend` as `vulkan`.

## Evidence Rows

The wrapper always emits:

- `electron_vulkan_web_parity_windows_status`
- `electron_vulkan_web_parity_windows_reason`
- `electron_vulkan_web_parity_windows_simple_bin`
- `electron_vulkan_web_parity_windows_simple_bin_source`
- `electron_vulkan_web_parity_windows_simple_bin_status`
- `electron_vulkan_web_parity_windows_host_os`
- `electron_vulkan_web_parity_windows_width`
- `electron_vulkan_web_parity_windows_height`

On a Windows host that reaches frame comparison it also emits:

- `electron_vulkan_web_parity_windows_electron_json`
- `electron_vulkan_web_parity_windows_vulkan_json`

## Completion Boundary

This contract does not prove a Windows GPU is available on the current Linux
developer host. It proves that the Windows wrapper cannot overstate missing
dependencies, non-Windows runs, Rust seed binaries, missing JSON outputs, pixel
mismatches, or a non-Vulkan Simple backend as a pass. Real completion still
requires running the wrapper on Windows with Electron installed and a
Vulkan-capable driver.

## Windows Operator Flow

1. Build or install a self-hosted Simple binary for Windows. Do not point
   `SIMPLE_BIN` at `src/compiler_rust/...`.
2. Install Electron dependencies in `tools/electron-shell` so the wrapper can
   launch `electron.cmd`.
3. Run the wrapper from a Windows shell with `OS=Windows_NT` already present in
   the environment.
4. Confirm the Electron capture produces `electron.json`.
5. Confirm the pure-Simple app writes `vulkan.json` through
   `src/app/test/electron_vulkan_web_parity.spl`.
6. Treat `reason=vulkan-backend-not-proven` as a hard failure: the Simple app
   ran, but the renderer did not prove the requested Vulkan backend.
7. Treat `reason=pixel-mismatch` as a renderer divergence: both paths produced
   frames, but the Vulkan-backed Simple frame differs from Chromium's Vulkan
   reference frame.
8. Treat `status=pass` and `reason=pixel-exact-vulkan` as the only successful
   Windows completion row for this wrapper.

## Failure Semantics

The wrapper separates absence from failure:

- `status=skip` means this host cannot run the Windows GUI/Vulkan evidence gate.
- `status=fail` means the gate reached a condition that would make Windows
  evidence invalid.
- `reason=simple-bin-forbidden` protects the pure-Simple requirement by
  rejecting the Rust bootstrap seed.
- `reason=electron-json-missing` protects the browser reference side.
- `reason=vulkan-json-missing` protects the Simple Vulkan renderer side.
- `reason=vulkan-backend-not-proven` protects against CPU, software, or other
  fallback renderers masquerading as Vulkan-backed GUI evidence.
- `reason=pixel-mismatch` protects the visual parity oracle.

## Relationship To Other Gates

This wrapper is narrower than the broader GUI RenderDoc and browser-backing
matrix gates. It does not inspect RenderDoc captures, browser GPU feature
status JSON, or host-window screenshots. Its job is to keep the Windows
Electron-vs-pure-Simple-Vulkan pixel parity lane honest and machine-readable.
The broader matrix may consume this evidence, but it must not reinterpret a
skip or fail row as a pass.

## Test Matrix

The spec contains:

- Static source inspection for typed evidence rows, seed rejection, dependency
  skip reasons, interpreter-mode execution, and Vulkan backend fail-closed
  comparison.
- A real local wrapper run that proves non-Windows hosts produce a structured
  skip while preserving Simple binary provenance.

## Scenarios

### Windows Electron Vulkan web parity wrapper

#### emits typed evidence rows and forbids seed Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-electron-vulkan-web-parity-windows.shs")

expect(script).to_contain("electron_vulkan_web_parity_windows_status")
expect(script).to_contain("electron_vulkan_web_parity_windows_reason")
expect(script).to_contain("simple-bin-forbidden")
expect(script).to_contain("requires-windows")
expect(script).to_contain("electron-missing")
expect(script).to_contain("node-missing")
expect(script).to_contain("SIMPLE_EXECUTION_MODE=interpret")
expect(script).to_contain("vulkan-json-missing")
expect(script).to_contain("v.backend!==\"vulkan\"")
expect(script).to_contain("vulkan-backend-not-proven")
```

</details>

#### skips cleanly on non-Windows hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", "EVWP_WORK=build/test-electron-vulkan-web-parity-windows-contract sh scripts/check/check-electron-vulkan-web-parity-windows.shs"])

expect(code).to_equal(0)
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_status=skip")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_reason=requires-windows")
expect(_stdout).to_contain("electron_vulkan_web_parity_windows_simple_bin_status=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md](doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md)
- **Research:** [doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md](doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md)


</details>
