# GUI Web 2D Vulkan Setup Simple Binary Selection

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 4 | 4 | 0 | 0 |

## Overview

This system spec validates the Simple binary discovery contract for
`scripts/setup/setup-gui-web-2d-vulkan-env.shs`, including the exact
`--renderdoc-simple` capture-to-gate evidence handoff.

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

## Simple RenderDoc Evidence Fields

- `gui_web_2d_vulkan_renderdoc_simple_source_env`
- `gui_web_2d_vulkan_renderdoc_simple_gate_evidence_env`
- `gui_web_2d_vulkan_renderdoc_simple_gate_status`
- `gui_web_2d_vulkan_renderdoc_simple_gate_reason`
- `gui_web_2d_vulkan_renderdoc_simple_status`
- `gui_web_2d_vulkan_renderdoc_simple_reason`

The host-independent system check inspects this source contract statically. It
does not claim a live RenderDoc capture or Simple runtime pass.

## Scenarios

### keeps PATH Simple fallback explicit and typed

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

### chains the exact Simple RenderDoc capture env into the strict gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

### prefers canonical pure Simple for default Vulkan evidence setup

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
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin=bin/simple")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin_selection_reason=repo-bin-canonical-self-hosted")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_bin_status=pass")
```

</details>

### rejects linked browser backing source proof files at the producer

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
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
