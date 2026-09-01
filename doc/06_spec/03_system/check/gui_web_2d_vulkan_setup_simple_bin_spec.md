# GUI Web 2D Vulkan Setup Simple Binary Selection

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

Clean jj worktrees may not have a repo-local `bin/simple` or git metadata for
same-repo PATH detection. The setup helper therefore supports PATH discovery
only when explicitly enabled with `ALLOW_PATH_SIMPLE_BIN=1`, and records the
selection reason in evidence.

## Operator Flow

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec validates the Simple binary discovery contract for
`scripts/setup/setup-gui-web-2d-vulkan-env.shs`.

Clean jj worktrees may not have a repo-local `bin/simple` or git metadata for
same-repo PATH detection. The setup helper therefore supports PATH discovery
only when explicitly enabled with `ALLOW_PATH_SIMPLE_BIN=1`, and records the
selection reason in evidence.

## Operator Flow

Run:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_vulkan_setup_simple_bin_spec.spl --mode=interpreter --clean --fail-fast
```

For a direct Vulkan artifact probe on such a worktree, use either an explicit
driver:

```sh
SIMPLE_BIN=/path/to/simple BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

or the opt-in PATH fallback:

```sh
ALLOW_PATH_SIMPLE_BIN=1 BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

For a direct Vulkan artifact probe on such a worktree, use either an explicit
driver:

```sh
SIMPLE_BIN=/path/to/simple BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

or the opt-in PATH fallback:

```sh
ALLOW_PATH_SIMPLE_BIN=1 BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

For a direct Vulkan artifact probe on such a worktree, use either an explicit
driver:

```sh
SIMPLE_BIN=/path/to/simple BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

or the opt-in PATH fallback:

```sh
ALLOW_PATH_SIMPLE_BIN=1 BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

For a direct Vulkan artifact probe on such a worktree, use either an explicit
driver:

```sh
SIMPLE_BIN=/path/to/simple BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

or the opt-in PATH fallback:

```sh
ALLOW_PATH_SIMPLE_BIN=1 BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

For a direct Vulkan artifact probe on such a worktree, use either an explicit
driver:

```sh
SIMPLE_BIN=/path/to/simple BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

or the opt-in PATH fallback:

```sh
ALLOW_PATH_SIMPLE_BIN=1 BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

For a direct Vulkan artifact probe on such a worktree, use either an explicit
driver:

```sh
SIMPLE_BIN=/path/to/simple BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

or the opt-in PATH fallback:

```sh
ALLOW_PATH_SIMPLE_BIN=1 BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

On a prepared RenderDoc host, the focused capture and strict replay gate are a
single fail-closed command:

```sh
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-renderdoc-simple \
  sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple
```

The capture produces
`build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`.
The wrapper passes that exact path as `RDOC_SIMPLE_EVIDENCE_ENV` to
`scripts/check/check-renderdoc-simple-gate.shs`, whose default canonical output
is `build/renderdoc/simple-gate/evidence.env`.

## Acceptance

- Same-repo PATH fallback remains available when git metadata can prove the
  binary belongs to the checkout.
- Generic PATH fallback requires `ALLOW_PATH_SIMPLE_BIN=1`.
- The opt-in fallback records
  `gui_web_2d_vulkan_simple_bin_selection_reason=default-missing-path-opt-in`.
- Evidence always emits `gui_web_2d_vulkan_simple_bin_selection_reason`.
- `--renderdoc-simple` cannot silently leave capture-only evidence: it invokes
  the strict gate with the exact produced source env and exits nonzero when
  capture or gate does not pass.
- The setup evidence relays the source/gate paths plus typed gate and aggregate
  status/reason fields.

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

Simple RenderDoc capture-to-gate setup must emit:

- `gui_web_2d_vulkan_renderdoc_simple_source_env`
- `gui_web_2d_vulkan_renderdoc_simple_gate_evidence_env`
- `gui_web_2d_vulkan_renderdoc_simple_gate_status`
- `gui_web_2d_vulkan_renderdoc_simple_gate_reason`
- `gui_web_2d_vulkan_renderdoc_simple_status`
- `gui_web_2d_vulkan_renderdoc_simple_reason`

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
9. `--renderdoc-simple` captures under the setup build directory, passes that
   exact generated `renderdoc/simple/evidence.env` to the strict gate, and
   writes the gate result to `build/renderdoc/simple-gate/evidence.env`.
10. Capture failure, gate failure, missing gate evidence, or any non-`pass`
    gate status emits a typed reason and makes the setup command exit nonzero.

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
- Static source inspection for the exact Simple capture-to-gate evidence path,
  canonical consumer output, typed status/reason relay, and nonzero failure.
- A real `--check` run that verifies default release Simple selection.
- A direct helper run with synthetic hardlinked and symlinked browser proof
  files to assert typed source statuses and fail-closed child rows.

## Scenarios

### GUI Web 2D Vulkan setup Simple binary selection

#### keeps PATH Simple fallback explicit and typed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps PATH Simple fallback explicit and typed
- Inspect setup Simple binary discovery contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps PATH Simple fallback explicit and typed")
val script = file_read("scripts/setup/setup-gui-web-2d-vulkan-env.shs")

step("Inspect setup Simple binary discovery contract")
expect(script).to_contain("same_repo_executable \"$path_simple_candidate\"")
expect(script).to_contain("default-missing-same-repo-path-fallback")
expect(script).to_contain("ALLOW_PATH_SIMPLE_BIN")
expect(script).to_contain("default-missing-path-opt-in")
expect(script).to_contain("gui_web_2d_vulkan_simple_bin_selection_reason")
expect(script).to_contain("Darwin:arm64|Darwin:aarch64")
expect(script).to_contain("release/x86_64-unknown-linux-gnu/simple")
expect(script).to_contain("simple_bin=\"bin/simple\"")
expect(script).to_contain("\"Simple v\"*")
expect(script).to_contain("repo-bin-canonical-self-hosted")
expect(script).to_contain("scripts/check/gui-web-2d-vulkan-browser-backing-status.js")
```

</details>

#### chains the exact Simple RenderDoc capture env into the strict gate

- chains the exact Simple RenderDoc capture env into the strict gate
- Inspect fail-closed Simple RenderDoc capture-to-gate contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains the exact Simple RenderDoc capture env into the strict gate")
val script = file_read("scripts/setup/setup-gui-web-2d-vulkan-env.shs")

step("Inspect fail-closed Simple RenderDoc capture-to-gate contract")
expect(script).to_contain("RDOC_SIMPLE_SOURCE_ENV=\"$RDOC_OUT/simple/evidence.env\"")
expect(script).to_contain("RDOC_SIMPLE_GATE_BUILD_DIR=\"${RDOC_SIMPLE_GATE_BUILD_DIR:-$ROOT_DIR/build/renderdoc/simple-gate}\"")
expect(script).to_contain("rm -f \"$RDOC_SIMPLE_SOURCE_ENV\" \"$RDOC_SIMPLE_GATE_BUILD_DIR/evidence.env\"")
expect(script.index_of("rm -f \"$RDOC_SIMPLE_SOURCE_ENV\"")).to_be_less_than(script.index_of("capture-simple >\"$BUILD_DIR/renderdoc-simple.out\""))
expect(script).to_contain("RDOC_SIMPLE_EVIDENCE_ENV=\"$RDOC_SIMPLE_SOURCE_ENV\"")
expect(script).to_contain("sh \"$ROOT_DIR/scripts/check/check-renderdoc-simple-gate.shs\"")
expect(script).to_contain("gui_web_2d_vulkan_renderdoc_simple_gate_status")
expect(script).to_contain("gui_web_2d_vulkan_renderdoc_simple_gate_reason")
expect(script).to_contain("[ \"$renderdoc_simple_status\" != pass ]")
```

</details>

#### prefers canonical pure Simple for default Vulkan evidence setup

- prefers canonical pure Simple for default Vulkan evidence setup
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prefers canonical pure Simple for default Vulkan evidence setup")
val root = "build/test-gui-web-2d-vulkan-setup-simple-bin-release"
val command = "rm -rf " + root + " && BUILD_DIR=" + root + " sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --check > " + root + ".out 2>&1"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin=bin/simple")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin_selection_reason=repo-bin-canonical-self-hosted")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin_status=pass")
```

</details>

#### rejects linked browser backing source proof files at the producer

- rejects linked browser backing source proof files at the producer
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects linked browser backing source proof files at the producer")
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
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
