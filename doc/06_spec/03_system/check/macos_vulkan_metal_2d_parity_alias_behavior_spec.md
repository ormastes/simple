# macOS Vulkan/Metal 2D parity alias safety

> Proves that the aggregate parity checker cannot overwrite either trusted input record through a direct path alias or a separate hard link to the same inode. Both scenarios verify rejection before the first write and compare the input bytes afterward.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS Vulkan/Metal 2D parity alias safety

Proves that the aggregate parity checker cannot overwrite either trusted input record through a direct path alias or a separate hard link to the same inode. Both scenarios verify rejection before the first write and compare the input bytes afterward.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/engine2d_four_backend_capture.md |
| Plan | doc/03_plan/sys_test/engine2d_four_backend_capture.md |
| Design | doc/05_design/engine2d_four_backend_capture.md |
| Research | doc/01_research/local/engine2d_four_backend_capture.md |
| Source | `test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl` |
| Updated | 2026-07-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that the aggregate parity checker cannot overwrite either trusted input
record through a direct path alias or a separate hard link to the same inode.
Both scenarios verify rejection before the first write and compare the input
bytes afterward.

**Requirements:** doc/02_requirements/feature/engine2d_four_backend_capture.md
**Plan:** doc/03_plan/sys_test/engine2d_four_backend_capture.md
**Design:** doc/05_design/engine2d_four_backend_capture.md
**Research:** doc/01_research/local/engine2d_four_backend_capture.md
**Architecture:** doc/04_architecture/engine2d_four_backend_capture.md

## Syntax

```sh
bin/simple test test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl --mode=interpreter
```

## Expected Result

The direct-alias and hard-link cases both fail closed while reporting that the
original Vulkan evidence hash is unchanged. This is a filesystem-safety
contract; it does not substitute for live Vulkan or Metal rendering evidence.

## Scenarios

### macOS Vulkan and Metal 2D parity output alias

#### should reject an output alias and preserve the input

- Construct two small valid lane records
- Select the Vulkan input as the aggregate output
- Require fail-closed rejection before any write
   - Expected: code equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct two small valid lane records")
step("Select the Vulkan input as the aggregate output")
step("Require fail-closed rejection before any write")
val (stdout, stderr, code) = process_run("/bin/sh", [
    "scripts/check/fixtures/check-macos-vulkan-metal-2d-parity-contract.shs",
    "--alias-only"
])
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("alias_status=fail")
expect(stdout).to_contain(
    "alias_reason=output-aliases-vulkan-evidence"
)
expect(stdout).to_contain("input_preserved=true")
```

</details>

#### should reject a hard-linked output and preserve the input

- Construct two small valid lane records
- Hard-link the aggregate output to the Vulkan input
- Require fail-closed rejection before any write
   - Expected: code equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct two small valid lane records")
step("Hard-link the aggregate output to the Vulkan input")
step("Require fail-closed rejection before any write")
val (stdout, stderr, code) = process_run("/bin/sh", [
    "scripts/check/fixtures/check-macos-vulkan-metal-2d-parity-contract.shs",
    "--hardlink-alias-only"
])
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("hardlink_alias_status=fail")
expect(stdout).to_contain(
    "hardlink_alias_reason=output-aliases-vulkan-evidence"
)
expect(stdout).to_contain("hardlink_input_preserved=true")
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

- **Requirements:** `doc/02_requirements/feature/engine2d_four_backend_capture.md`
- **Plan:** `doc/03_plan/sys_test/engine2d_four_backend_capture.md`
- **Design:** `doc/05_design/engine2d_four_backend_capture.md`
- **Research:** `doc/01_research/local/engine2d_four_backend_capture.md`


</details>
