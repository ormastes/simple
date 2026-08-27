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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject an output alias and preserve the input
- Construct two small valid lane records
- Select the Vulkan input as the aggregate output
- Require fail-closed rejection before any write
   - Expected: code equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an output alias and preserve the input")
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

- should reject a hard-linked output and preserve the input
- Construct two small valid lane records
- Hard-link the aggregate output to the Vulkan input
- Require fail-closed rejection before any write
   - Expected: code equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a hard-linked output and preserve the input")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e288c3a0af97353564a8205e74a0a565904c6a97106eae64bb73df51dabad2a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e288c3a0af97353564a8205e74a0a565904c6a97106eae64bb73df51dabad2a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e288c3a0af97353564a8205e74a0a565904c6a97106eae64bb73df51dabad2a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl
mirror: doc/06_spec/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an output alias and preserve the input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an output alias and preserve the input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a hard-linked output and preserve the input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/macos_vulkan_metal_2d_parity_alias_behavior_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a hard-linked output and preserve the input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
