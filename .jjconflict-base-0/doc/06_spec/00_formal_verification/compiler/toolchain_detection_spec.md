# Toolchain Detection Specification

> <details>

<!-- sdn-diagram:id=toolchain_detection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=toolchain_detection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

toolchain_detection_spec -> std
toolchain_detection_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=toolchain_detection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Toolchain Detection Specification

## Scenarios

### Toolchain Detection

#### detects whether Lean is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = toolchain.ToolchainInfo.detect()
val status = info.format_status()
expect(status).to_contain("Lean Toolchain Status:")
expect(status).to_contain("Lean:")
expect(status).to_contain("Lake:")
```

</details>

#### reports version_match true when no lean-toolchain file and lean is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = toolchain.ToolchainInfo.detect()
# If lean is available but no lean-toolchain, version_match should be true
if info.lean_available and not info.expected_version.?:
    expect(info.version_match).to_equal(true)
```

</details>

#### produces a non-empty format_status

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = toolchain.ToolchainInfo.detect()
val status = info.format_status()
expect(status.len()).to_be_greater_than(0)
expect(status).to_contain("Lean Toolchain Status:")
```

</details>

#### ToolchainError messages

#### LeanNotFound message is human-readable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = toolchain.ToolchainError.LeanNotFound
val msg = err.to_string()
expect(msg).to_contain("Lean 4 not found")
expect(msg).to_contain("https://leanprover.github.io/lean4/")
```

</details>

#### LakeNotFound message mentions Lake

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = toolchain.ToolchainError.LakeNotFound
expect(err.to_string()).to_contain("Lake not found")
```

</details>

#### VersionMismatch message is descriptive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = toolchain.ToolchainError.VersionMismatch
expect(err.to_string()).to_contain("does not match")
```

</details>

#### ProjectInvalid message mentions lakefile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = toolchain.ToolchainError.ProjectInvalid
expect(err.to_string()).to_contain("lakefile.lean")
```

</details>

#### DependencyError message mentions dependency

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = toolchain.ToolchainError.DependencyError
expect(err.to_string()).to_contain("dependency")
```

</details>

#### validate_toolchain

#### returns ProjectInvalid for nonexistent directory

1. or msg contains
2. or msg contains
   - Expected: is_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = toolchain.validate_toolchain("/nonexistent/path/no_project_here")
# If lean+lake are installed, we get ProjectInvalid.
# If lean is not installed, we get LeanNotFound.
# Either way, it should be an Err.
match result:
    case Ok(_):
        expect("validate_toolchain unexpectedly accepted a nonexistent project").to_equal("")
    case Err(err):
        val msg = err.to_string()
        # Must be one of the known error messages
        val is_known = (msg.contains("Lean 4 not found")
            or msg.contains("Lake not found")
            or msg.contains("lakefile.lean"))
        expect(is_known).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/toolchain_detection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Toolchain Detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
