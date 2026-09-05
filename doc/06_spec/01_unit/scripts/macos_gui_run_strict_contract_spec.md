# Macos Gui Run Strict Contract Specification

> Tests covering macOS GUI strict launcher contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Gui Run Strict Contract Specification

## Scenarios

### macOS GUI strict launcher contract

#### has no caller-authored host-neutral admission bypass

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has no caller-authored host-neutral admission bypass
   - Expected: launcher does not contain `SIMPLE_GUI_STRICT_CONTRACT_PROBE`
   - Expected: launcher does not contain `SIMPLE_GUI_STRICT_PROBE_ADMISSION_PATH`
   - Expected: launcher does not contain `assert_no_simple_seed_descendant`
   - Expected: launcher does not contain `*/bootstrap/*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("has no caller-authored host-neutral admission bypass")
val launcher = file_read("scripts/gui/macos-gui-run.shs")
expect(launcher.contains("SIMPLE_GUI_STRICT_CONTRACT_PROBE")).to_equal(false)
expect(launcher.contains("SIMPLE_GUI_STRICT_PROBE_ADMISSION_PATH")).to_equal(false)
expect(launcher).to_contain("selected binary changed during bundle copy")
expect(launcher).to_contain("bundled binary hash differs from selected binary")
expect(launcher.contains("assert_no_simple_seed_descendant")).to_equal(false)
expect(launcher.contains("*/bootstrap/*")).to_equal(false)
expect(launcher).to_contain("strict_admitted_gui_driver")
```

</details>

#### records strict binary and process identities in a versioned receipt

- records strict binary and process identities in a versioned receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("records strict binary and process identities in a versioned receipt")
val launcher = file_read("scripts/gui/macos-gui-run.shs")
expect(launcher).to_contain("SIMPLE_NO_BOOTSTRAP_DELEGATE")
expect(launcher).to_contain(
    "no_bootstrap_delegate=\"" + SHELL_OPEN +
        "SIMPLE_NO_BOOTSTRAP_DELEGATE:-0}\""
)
expect(launcher).to_contain("schema=macos_gui_run_pid_receipt_v3")
expect(launcher).to_contain("selected_binary_hash")
expect(launcher).to_contain("bundled_binary_hash")
expect(launcher).to_contain("trusted_manifest_hash")
expect(launcher).to_contain("trusted_gui_driver_source_kind")
expect(launcher).to_contain("trusted_gui_driver_sha256")
expect(launcher).to_contain("launcher_executable")
expect(launcher).to_contain("window_owner_executable")
```

</details>

#### requires real manifest admission in strict launch mode

- requires real manifest admission in strict launch mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("requires real manifest admission in strict launch mode")
val launcher = file_read("scripts/gui/macos-gui-run.shs")
expect(launcher).to_contain(
    "scripts/check/lib/macos-gpu-trusted-build-admission.shs"
)
expect(launcher).to_contain("macos_gpu_full_cli_gui_admit")
expect(launcher).to_contain(
    "build/bootstrap/full/$platform/provenance/gui-driver.env"
)
expect(launcher).to_contain("SIMPLE_GUI_TRUSTED_MANIFEST_PATH")
expect(launcher).to_contain(
    "[[ \"$override_candidate\" = \"$strict_admitted_gui_driver\" ]]"
)
expect(launcher).to_contain(
    "\"$strict_admitted_gui_driver_hash\""
)
expect(launcher).to_contain(
    "MACOS_GPU_ADMISSION_GUI_DRIVER_SHA256"
)
expect(launcher).to_contain(
    "MACOS_GPU_ADMISSION_MANIFEST_SHA256"
)
expect(launcher).to_contain(
    "assert_strict_admitted_inputs_unchanged"
)
```

</details>

#### fails closed on a host without bypassing canonical admission

- fails closed on a host without bypassing canonical admission
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("fails closed on a host without bypassing canonical admission")
val command = "SIMPLE_GUI_STRICT_EVIDENCE=1 " +
    "SIMPLE_NO_BOOTSTRAP_DELEGATE=1 SIMPLE_GUI_BINARY=/usr/bin/env " +
    "bash scripts/gui/macos-gui-run.shs"
val (_out, _err, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/macos_gui_run_strict_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering macOS GUI strict launcher contract.
- macOS GUI strict launcher contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SCRIPTS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55bd06800d6079517280b2b8604ac4bd8750503c29b15e8c3d2d844f829a6691`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55bd06800d6079517280b2b8604ac4bd8750503c29b15e8c3d2d844f829a6691`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55bd06800d6079517280b2b8604ac4bd8750503c29b15e8c3d2d844f829a6691`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/scripts/macos_gui_run_strict_contract_spec.spl
mirror: doc/06_spec/01_unit/scripts/macos_gui_run_strict_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/macos_gui_run_strict_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/macos_gui_run_strict_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/macos_gui_run_strict_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/scripts/macos_gui_run_strict_contract_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no caller-authored host-neutral admission bypass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/macos_gui_run_strict_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records strict binary and process identities in a versioned receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/macos_gui_run_strict_contract_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires real manifest admission in strict launch mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
