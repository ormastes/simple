# GUI Web 2D Vulkan Setup Simple Binary Selection

> Validates the Simple binary discovery contract for `scripts/setup/setup-gui-web-2d-vulkan-env.shs`. Clean jj worktrees may not have a repo-local `bin/simple` or git metadata for same-repo detection, so PATH fallback must exist but remain explicit.

<!-- sdn-diagram:id=gui_web_2d_vulkan_setup_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_vulkan_setup_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_vulkan_setup_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_vulkan_setup_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Web 2D Vulkan Setup Simple Binary Selection

Validates the Simple binary discovery contract for `scripts/setup/setup-gui-web-2d-vulkan-env.shs`. Clean jj worktrees may not have a repo-local `bin/simple` or git metadata for same-repo detection, so PATH fallback must exist but remain explicit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md |
| Research | doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md |
| Source | `test/03_system/check/gui_web_2d_vulkan_setup_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Simple binary discovery contract for
`scripts/setup/setup-gui-web-2d-vulkan-env.shs`. Clean jj worktrees may not have
a repo-local `bin/simple` or git metadata for same-repo detection, so PATH
fallback must exist but remain explicit.

This spec also covers the producer-side browser-backing source-file contract.
The setup wrapper writes `gui_web_2d_vulkan_*_browser_backing_*` rows during
`--browser-backing` runs. Those rows are later consumed by the aggregate GUI
RenderDoc audit, Linux Vulkan render-log comparison, and platform matrix
criteria. A child browser pass must therefore prove both GPU state and the
source proof artifact shape. A copied, linked, empty, or directory-shaped proof
file is diagnostics only, not completion evidence.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md
**Design:** doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_vulkan_setup_simple_bin_spec.spl --mode=interpreter --clean --fail-fast
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
node scripts/check/gui-web-2d-vulkan-browser-backing-status.js \
  build/gui-web-2d-vulkan-env/electron_argb_proof.json \
  build/gui-web-2d-vulkan-env/electron_argb.json \
  build/gui-web-2d-vulkan-env/chrome_argb_proof.json
```

## Acceptance

- PATH `simple` fallback is gated by `ALLOW_PATH_SIMPLE_BIN=1`.
- The opt-in path records `default-missing-path-opt-in`.
- Existing same-repo PATH fallback remains available when git metadata can
  prove the binary belongs to the checkout.
- Default discovery prefers release self-hosted binaries before the `bin/simple`
  shim when a release binary exists.
- Browser-backing source proof files are typed as `symlink`, `hardlink`,
  `not-regular`, `empty`, `missing`, or `pass`; child browser-backing passes
  require regular single-link proof files.

## Evidence Fields

Simple binary selection must emit:

- `gui_web_2d_vulkan_simple_bin`
- `gui_web_2d_vulkan_simple_bin_selection_reason`
- `gui_web_2d_vulkan_simple_bin_status`

Browser-backing source classification must emit:

- `gui_web_2d_vulkan_electron_browser_backing_source`
- `gui_web_2d_vulkan_electron_browser_backing_source_file_status`
- `gui_web_2d_vulkan_electron_browser_backing_argb_source`
- `gui_web_2d_vulkan_electron_browser_backing_argb_source_file_status`
- `gui_web_2d_vulkan_chrome_browser_backing_source`
- `gui_web_2d_vulkan_chrome_browser_backing_source_file_status`
- `gui_web_2d_vulkan_electron_browser_backing_status`
- `gui_web_2d_vulkan_chrome_browser_backing_status`
- `gui_web_2d_vulkan_browser_backing_status`

## Source Status Semantics

The browser-backing helper uses `lstat` semantics so it can identify a link
itself instead of following the link and accidentally validating the target.
Status meanings:

- `pass`: regular proof file, nonempty, single link.
- `missing`: path does not exist.
- `unavailable`: producer had no path to check.
- `symlink`: path is a symbolic link.
- `hardlink`: path is a regular file with more than one link.
- `not-regular`: path exists but is not a regular file.
- `empty`: regular single-link file exists but has zero bytes.

Only `pass` may support a child browser-backing pass. Other statuses must force
the corresponding child status to `fail` with a source-file reason.

## Producer Flow

1. Run `--check` to capture host readiness, Simple binary selection, loader
   status, and RenderDoc discovery.
2. Run `--browser-backing` on a real GUI/Vulkan host to launch Electron and
   Chrome with Vulkan-requesting flags and capture compact GPU proof JSON.
3. The setup script calls
   `scripts/check/gui-web-2d-vulkan-browser-backing-status.js` with Electron
   proof, Electron ARGB proof, and Chrome proof paths.
4. The helper reads GPU feature status and GPU aux attributes.
5. The helper classifies proof files with `lstat`.
6. Electron passes only when Vulkan is enabled, GPU compositing is enabled,
   hardware Vulkan support is true, Vulkan appears in renderer metadata, and
   the Electron source proof file status is `pass`.
7. Chrome passes only when GPU compositing is enabled, hardware Vulkan support
   is true, Vulkan appears in renderer metadata, and the Chrome source proof
   file status is `pass`.
8. The top-level browser-backing row passes only when both child rows pass.

## Failure Examples

- A hardlinked Electron proof emits
  `gui_web_2d_vulkan_electron_browser_backing_source_file_status=hardlink` and
  `gui_web_2d_vulkan_electron_browser_backing_reason=electron-source-file-hardlink`.
- A symlinked Electron ARGB proof emits
  `gui_web_2d_vulkan_electron_browser_backing_argb_source_file_status=symlink`.
- A hardlinked Chrome proof emits
  `gui_web_2d_vulkan_chrome_browser_backing_source_file_status=hardlink` and
  `gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-source-file-hardlink`.
- Missing Node leaves the setup wrapper with
  `gui_web_2d_vulkan_browser_backing_reason=missing-node`.

## Completion Boundary

This spec does not prove that this host has a Vulkan-backed Electron or Chrome
session. It proves that the setup producer cannot overstate linked proof files
as valid completion evidence. Real completion still requires a prepared Linux,
macOS, or Windows GUI host to produce live browser-backing rows, pairwise ARGB
comparison evidence, Simple backend evidence, and RenderDoc or native GPU
debugger artifacts.

## Test Matrix

The spec contains:

- Static source inspection for Simple binary discovery and helper routing.
- A real `--check` run that verifies default release Simple selection.
- A direct helper run with synthetic hardlinked and symlinked browser proof
  files to assert typed source statuses and fail-closed child rows.

## Scenarios

### GUI Web 2D Vulkan setup Simple binary selection

#### keeps PATH Simple fallback explicit and typed

- Inspect setup Simple binary discovery contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/setup/setup-gui-web-2d-vulkan-env.shs")

step("Inspect setup Simple binary discovery contract")
expect(script).to_contain("same_repo_executable \"$path_simple_candidate\"")
expect(script).to_contain("default-missing-same-repo-path-fallback")
expect(script).to_contain("ALLOW_PATH_SIMPLE_BIN")
expect(script).to_contain("default-missing-path-opt-in")
expect(script).to_contain("gui_web_2d_vulkan_simple_bin_selection_reason")
expect(script).to_contain("release/x86_64-unknown-linux-gnu/simple")
expect(script).to_contain("simple_bin=\"bin/simple\"")
expect(script).to_contain("scripts/check/gui-web-2d-vulkan-browser-backing-status.js")
```

</details>

#### prefers release Simple for default Vulkan evidence setup

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-web-2d-vulkan-setup-simple-bin-release"
val command = "rm -rf " + root + " && BUILD_DIR=" + root + " sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --check > " + root + ".out 2>&1"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin=release/x86_64-unknown-linux-gnu/simple")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin_selection_reason=self-hosted-release")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin_status=pass")
```

</details>

#### rejects linked browser backing source proof files at the producer

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-web-2d-vulkan-browser-backing-linked-sources"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '{\"gpu_feature_status\":{\"vulkan\":\"enabled\",\"gpu_compositing\":\"enabled\"},\"browser_target_gpu_info\":{\"gpu\":{\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}' > " + root + "/electron-proof-original.json && ln " + root + "/electron-proof-original.json " + root + "/electron-proof.json && printf '{}\\n' > " + root + "/electron-argb-target.json && ln -s electron-argb-target.json " + root + "/electron-argb.json && printf '%s\\n' '{\"gpu_info\":{\"gpu\":{\"featureStatus\":{\"gpu_compositing\":\"enabled\"},\"auxAttributes\":{\"hardwareSupportsVulkan\":true,\"displayType\":\"Vulkan\",\"glImplementationParts\":\"angle=vulkan\",\"skiaBackendType\":\"Vulkan\",\"glRenderer\":\"Vulkan\"}}}}' > " + root + "/chrome-proof-original.json && ln " + root + "/chrome-proof-original.json " + root + "/chrome-proof.json && node scripts/check/gui-web-2d-vulkan-browser-backing-status.js " + root + "/electron-proof.json " + root + "/electron-argb.json " + root + "/chrome-proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("gui_web_2d_vulkan_browser_backing_status=fail")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_browser_backing_source_file_status=hardlink")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_browser_backing_argb_source_file_status=symlink")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_browser_backing_status=fail")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_browser_backing_reason=electron-source-file-hardlink")
expect(evidence).to_contain("gui_web_2d_vulkan_chrome_browser_backing_source_file_status=hardlink")
expect(evidence).to_contain("gui_web_2d_vulkan_chrome_browser_backing_status=fail")
expect(evidence).to_contain("gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-source-file-hardlink")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md](doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md)
- **Research:** [doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md](doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md)


</details>
