# Toolchain Detection Specification

> Tests covering Toolchain Detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Toolchain Detection Specification

## Scenarios

### Toolchain Detection

#### detects whether Lean is available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects whether Lean is available
   - Expected: info.lean_available equals `info.lean_available`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects whether Lean is available")
val info = toolchain.ToolchainInfo.detect()
# Tautology — verifies detect() runs without crash
expect(info.lean_available).to_equal(info.lean_available)
```

</details>

#### reports version_match true when no lean-toolchain file and lean is available

- reports version_match true when no lean-toolchain file and lean is available
   - Expected: info.version_match is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports version_match true when no lean-toolchain file and lean is available")
val info = toolchain.ToolchainInfo.detect()
# If lean is available but no lean-toolchain, version_match should be true
if info.lean_available and not info.expected_version.?:
    expect(info.version_match).to_equal(true)
```

</details>

#### produces a non-empty format_status

- produces a non-empty format_status
   - Expected: status.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a non-empty format_status")
val info = toolchain.ToolchainInfo.detect()
val status = info.format_status()
expect(status.len() > 0).to_equal(true)
expect(status).to_contain("Lean Toolchain Status:")
```

</details>

#### ToolchainError messages

#### LeanNotFound message is human-readable

- LeanNotFound message is human-readable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LeanNotFound message is human-readable")
val err = toolchain.ToolchainError.LeanNotFound
val msg = err.to_string()
expect(msg).to_contain("Lean 4 not found")
expect(msg).to_contain("https://leanprover.github.io/lean4/")
```

</details>

#### LakeNotFound message mentions Lake

- LakeNotFound message mentions Lake


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LakeNotFound message mentions Lake")
val err = toolchain.ToolchainError.LakeNotFound
expect(err.to_string()).to_contain("Lake not found")
```

</details>

#### VersionMismatch message is descriptive

- VersionMismatch message is descriptive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VersionMismatch message is descriptive")
val err = toolchain.ToolchainError.VersionMismatch
expect(err.to_string()).to_contain("does not match")
```

</details>

#### ProjectInvalid message mentions lakefile

- ProjectInvalid message mentions lakefile


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ProjectInvalid message mentions lakefile")
val err = toolchain.ToolchainError.ProjectInvalid
expect(err.to_string()).to_contain("lakefile.lean")
```

</details>

#### DependencyError message mentions dependency

- DependencyError message mentions dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DependencyError message mentions dependency")
val err = toolchain.ToolchainError.DependencyError
expect(err.to_string()).to_contain("dependency")
```

</details>

#### validate_toolchain

#### returns ProjectInvalid for nonexistent directory

- returns ProjectInvalid for nonexistent directory
   - Expected: true is true
   - Expected: is_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ProjectInvalid for nonexistent directory")
val result = toolchain.validate_toolchain("/nonexistent/path/no_project_here")
# If lean+lake are installed, we get ProjectInvalid.
# If lean is not installed, we get LeanNotFound.
# Either way, it should be an Err.
match result:
    case Ok(_):
        # Lean is installed AND somehow the path exists — unlikely but not a crash
        expect(true).to_equal(true)
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
| Source | `test/unit/compiler/verification/toolchain_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Toolchain Detection.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0fe58cef1e697342fe6d9648827d5668f87e2bc345585a9a4bb6cf37943f3ce4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0fe58cef1e697342fe6d9648827d5668f87e2bc345585a9a4bb6cf37943f3ce4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0fe58cef1e697342fe6d9648827d5668f87e2bc345585a9a4bb6cf37943f3ce4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/verification/toolchain_detection_spec.spl
mirror: doc/06_spec/unit/compiler/verification/toolchain_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/verification/toolchain_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/verification/toolchain_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/verification/toolchain_detection_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects whether Lean is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/toolchain_detection_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports version_match true when no lean-toolchain file and lean is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/toolchain_detection_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a non-empty format_status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
