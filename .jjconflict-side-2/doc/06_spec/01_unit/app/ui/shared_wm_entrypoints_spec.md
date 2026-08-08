# Shared Wm Entrypoints Specification

> <details>

<!-- sdn-diagram:id=shared_wm_entrypoints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_wm_entrypoints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_wm_entrypoints_spec -> std
shared_wm_entrypoints_spec -> os
shared_wm_entrypoints_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_wm_entrypoints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Wm Entrypoints Specification

## Scenarios

### shared WM entrypoint CLI/env precedence

#### electron honors --shared-wm and SIMPLE_UI_ELECTRON_SHARED_WM

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_requested_electron([], "")).to_equal(false)
expect(shared_wm_requested_electron([], "0")).to_equal(false)
expect(shared_wm_requested_electron([], "1")).to_equal(true)
expect(shared_wm_requested_electron(["--shared-wm"], "0")).to_equal(true)
```

</details>

#### tauri honors --shared-wm and SIMPLE_UI_TAURI_SHARED_WM

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_requested_tauri([], "")).to_equal(false)
expect(shared_wm_requested_tauri([], "0")).to_equal(false)
expect(shared_wm_requested_tauri([], "1")).to_equal(true)
expect(shared_wm_requested_tauri(["--shared-wm"], "0")).to_equal(true)
```

</details>

#### tui honors --shared-wm and SIMPLE_UI_TUI_SHARED_WM

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_requested_tui([], "")).to_equal(false)
expect(shared_wm_requested_tui([], "0")).to_equal(false)
expect(shared_wm_requested_tui([], "1")).to_equal(true)
expect(shared_wm_requested_tui(["--shared-wm"], "0")).to_equal(true)
```

</details>

#### browser honors --shared-wm and SIMPLE_UI_BROWSER_SHARED_WM

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_requested_browser([], "")).to_equal(false)
expect(shared_wm_requested_browser([], "0")).to_equal(false)
expect(shared_wm_requested_browser([], "1")).to_equal(true)
expect(shared_wm_requested_browser(["--shared-wm"], "0")).to_equal(true)
```

</details>

#### web honors --shared-wm and SIMPLE_UI_WEB_SHARED_WM

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_requested_web([], "")).to_equal(false)
expect(shared_wm_requested_web([], "0")).to_equal(false)
expect(shared_wm_requested_web([], "1")).to_equal(true)
expect(shared_wm_requested_web(["--shared-wm"], "0")).to_equal(true)
```

</details>

#### tui_web honors --shared-wm and SIMPLE_UI_TUI_WEB_SHARED_WM

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_requested_tui_web([], "")).to_equal(false)
expect(shared_wm_requested_tui_web([], "0")).to_equal(false)
expect(shared_wm_requested_tui_web([], "1")).to_equal(true)
expect(shared_wm_requested_tui_web(["--shared-wm"], "0")).to_equal(true)
```

</details>

### shared WM entrypoint HostBackendKind matrix

#### maps six entrypoints to their documented shared WM backend kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_backend_kind_electron()).to_equal(HostBackendKind.Electron)
expect(shared_wm_backend_kind_tauri()).to_equal(HostBackendKind.Tauri)
expect(shared_wm_backend_kind_tui()).to_equal(HostBackendKind.Tui)
expect(shared_wm_backend_kind_browser()).to_equal(HostBackendKind.Browser)
# ui.web currently boots the HTTP/WebCanvas WM shell rather than a
# blocking init_host_wm loop; this helper preserves the expected
# HostBackendKind handoff for the shared entrypoint matrix.
expect(shared_wm_backend_kind_web()).to_equal(HostBackendKind.WebCanvas)
expect(shared_wm_backend_kind_tui_web()).to_equal(HostBackendKind.Tui)
```

</details>

#### documents current selector fallback for Browser Electron WebCanvas and Tui

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_host_backend_selector(shared_wm_backend_kind_electron())).to_equal(0)
expect(_host_backend_selector(shared_wm_backend_kind_tauri())).to_equal(0)
expect(_host_backend_selector(shared_wm_backend_kind_tui())).to_equal(0)
expect(_host_backend_selector(shared_wm_backend_kind_browser())).to_equal(0)
expect(_host_backend_selector(shared_wm_backend_kind_web())).to_equal(0)
expect(_host_backend_selector(shared_wm_backend_kind_tui_web())).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/shared_wm_entrypoints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared WM entrypoint CLI/env precedence
- shared WM entrypoint HostBackendKind matrix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
