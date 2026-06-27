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
| 1 | 1 | 0 | 0 |

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

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md
**Design:** doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_vulkan_setup_simple_bin_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- PATH `simple` fallback is gated by `ALLOW_PATH_SIMPLE_BIN=1`.
- The opt-in path records `default-missing-path-opt-in`.
- Existing same-repo PATH fallback remains available when git metadata can
  prove the binary belongs to the checkout.

## Scenarios

### GUI Web 2D Vulkan setup Simple binary selection

#### keeps PATH Simple fallback explicit and typed

- Inspect setup Simple binary discovery contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/setup/setup-gui-web-2d-vulkan-env.shs")

step("Inspect setup Simple binary discovery contract")
expect(script).to_contain("same_repo_executable \"$path_simple_candidate\"")
expect(script).to_contain("default-missing-same-repo-path-fallback")
expect(script).to_contain("ALLOW_PATH_SIMPLE_BIN")
expect(script).to_contain("default-missing-path-opt-in")
expect(script).to_contain("gui_web_2d_vulkan_simple_bin_selection_reason")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md](doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md)
- **Research:** [doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md](doc/09_report/gui_renderdoc_web_wm_path_fallback_evidence_2026-06-27.md)


</details>
