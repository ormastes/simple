# Debug Sidecar JSON Key-Order Specification

> Verifies that the generated `*.debug.json` sidecar files produced by the FPGA Linux generation scripts maintain their exact key order after the MDSOC capsule reorganization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Sidecar JSON Key-Order Specification

Verifies that the generated `*.debug.json` sidecar files produced by the FPGA Linux generation scripts maintain their exact key order after the MDSOC capsule reorganization.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #rtl-mdsoc-reorg |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md |
| Design | doc/05_design/rtl_riscv_mdsoc_capsules.md |
| Source | `test/system/compiler/debug_sidecar_json_order_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the generated `*.debug.json` sidecar files produced by the FPGA
Linux generation scripts maintain their exact key order after the MDSOC
capsule reorganization.

The `debug_sidecar_json` function in `fpga_linux_manifest.spl` emits JSON via
string concatenation in literal source order. This is an immutable contract —
no serializer, no key shuffling allowed.

## Key Order Contract (AC-3, D-4)

Expected JSON key order:
1. `reportMarkers`
2. `runnerSuccessMarkers`
3. `sourceMap`
4. `proofLane` (header field)

The exact expected order is recorded in the baseline at:
`doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md`

Pending: tests that require the baseline are gated on SA-1 creating it.

## Acceptance Criteria

- AC-3: *.debug.json sidecar contract preserved (reportMarkers,
  runnerSuccessMarkers byte-equivalent)
- AC-8: Verify in interpreter mode

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `rtl_mdsoc_baseline_2026-05-02.md` | Artifact | `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md` |

## Scenarios

### Debug Sidecar JSON Key Order: source contract (AC-3, D-4)

#### AC-3: fpga_linux_manifest.spl contains reportMarkers key string

- AC-3: fpga_linux_manifest.spl contains reportMarkers key string
   - Expected: has_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: fpga_linux_manifest.spl contains reportMarkers key string")
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val content = read_file(path)
val has_key = content.contains("reportMarkers")
expect(has_key).to_equal(true)
```

</details>

#### AC-3: fpga_linux_manifest.spl contains runnerSuccessMarkers key string

- AC-3: fpga_linux_manifest.spl contains runnerSuccessMarkers key string
   - Expected: has_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: fpga_linux_manifest.spl contains runnerSuccessMarkers key string")
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val content = read_file(path)
val has_key = content.contains("runnerSuccessMarkers")
expect(has_key).to_equal(true)
```

</details>

#### AC-3: reportMarkers appears before runnerSuccessMarkers in manifest source

- AC-3: reportMarkers appears before runnerSuccessMarkers in manifest source


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: reportMarkers appears before runnerSuccessMarkers in manifest source")
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val pos_report = source_key_offset("reportMarkers")
val pos_runner = source_key_offset("runnerSuccessMarkers")
check_msg(pos_report >= 0, "reportMarkers not found in manifest source")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in manifest source")
check_msg(pos_report < pos_runner, "reportMarkers must appear before runnerSuccessMarkers in source")
expect(pos_report).to_be_less_than(pos_runner)
```

</details>

#### AC-3: sourceMap appears after runnerSuccessMarkers in manifest source

- AC-3: sourceMap appears after runnerSuccessMarkers in manifest source


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: sourceMap appears after runnerSuccessMarkers in manifest source")
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val pos_runner = source_key_offset("runnerSuccessMarkers")
val pos_source_map = source_key_offset("sourceMap")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in manifest source")
check_msg(pos_source_map >= 0, "sourceMap not found in manifest source")
check_msg(pos_runner < pos_source_map, "runnerSuccessMarkers must appear before sourceMap in source")
expect(pos_runner).to_be_less_than(pos_source_map)
```

</details>

#### AC-3: D-4 invariant — no json_ helper functions exist outside fpga_linux_manifest.spl

- AC-3: D-4 invariant — no json_ helper functions exist outside fpga_linux_manifest.spl
   - Expected: has_json_helper is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: D-4 invariant — no json_ helper functions exist outside fpga_linux_manifest.spl")
# The D-4 decision states all json_* helpers live exclusively in
# fpga_linux_manifest.spl. Verify that fpga_linux_orchestrator.spl
# does not contain json_ helper definitions.
val path = orchestrator_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val content = read_file(path)
val has_json_helper = content.contains("fn json_")
check_msg(not has_json_helper, "D-4 violation: json_ helper defined in orchestrator, must be in manifest only")
expect(has_json_helper).to_equal(false)
```

</details>

### Debug Sidecar JSON Key Order: generated output (AC-3)

#### AC-3: RV32 generated debug.json key-order check is pending until SA-3 complete

- AC-3: RV32 generated debug.json key-order check is pending until SA-3 complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV32 generated debug.json key-order check is pending until SA-3 complete")
pending("SA-3 gate — build output not yet generated by split scripts")
```

</details>

#### AC-3: RV32 generated debug.json has reportMarkers key

- AC-3: RV32 generated debug.json has reportMarkers key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV32 generated debug.json has reportMarkers key")
if not rt_file_exists(rv32_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos = debug_json_key_offset(rv32_build_dir(), "reportMarkers")
check_msg(pos >= 0, "reportMarkers missing from generated debug.json in " + rv32_build_dir())
expect(pos).to_be_greater_than(-1)
```

</details>

#### AC-3: RV32 generated debug.json has runnerSuccessMarkers key

- AC-3: RV32 generated debug.json has runnerSuccessMarkers key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV32 generated debug.json has runnerSuccessMarkers key")
if not rt_file_exists(rv32_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos = debug_json_key_offset(rv32_build_dir(), "runnerSuccessMarkers")
check_msg(pos >= 0, "runnerSuccessMarkers missing from generated debug.json in " + rv32_build_dir())
expect(pos).to_be_greater_than(-1)
```

</details>

#### AC-3: RV32 generated debug.json reportMarkers precedes runnerSuccessMarkers

- AC-3: RV32 generated debug.json reportMarkers precedes runnerSuccessMarkers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV32 generated debug.json reportMarkers precedes runnerSuccessMarkers")
if not rt_file_exists(rv32_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos_report = debug_json_key_offset(rv32_build_dir(), "reportMarkers")
val pos_runner = debug_json_key_offset(rv32_build_dir(), "runnerSuccessMarkers")
check_msg(pos_report >= 0, "reportMarkers not found in generated json")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in generated json")
expect(pos_report).to_be_less_than(pos_runner)
```

</details>

#### AC-3: RV64 generated debug.json key-order check is pending until SA-3 complete

- AC-3: RV64 generated debug.json key-order check is pending until SA-3 complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV64 generated debug.json key-order check is pending until SA-3 complete")
pending("SA-3 gate — build output not yet generated by split scripts")
```

</details>

#### AC-3: RV64 generated debug.json has reportMarkers key

- AC-3: RV64 generated debug.json has reportMarkers key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV64 generated debug.json has reportMarkers key")
if not rt_file_exists(rv64_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos = debug_json_key_offset(rv64_build_dir(), "reportMarkers")
check_msg(pos >= 0, "reportMarkers missing from generated debug.json in " + rv64_build_dir())
expect(pos).to_be_greater_than(-1)
```

</details>

#### AC-3: RV64 generated debug.json reportMarkers precedes runnerSuccessMarkers

- AC-3: RV64 generated debug.json reportMarkers precedes runnerSuccessMarkers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV64 generated debug.json reportMarkers precedes runnerSuccessMarkers")
if not rt_file_exists(rv64_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos_report = debug_json_key_offset(rv64_build_dir(), "reportMarkers")
val pos_runner = debug_json_key_offset(rv64_build_dir(), "runnerSuccessMarkers")
check_msg(pos_report >= 0, "reportMarkers not found in generated json")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in generated json")
expect(pos_report).to_be_less_than(pos_runner)
```

</details>

### Debug Sidecar JSON Order: baseline comparison (AC-3)

#### AC-3: debug.json sha256 comparison is pending until SA-1 baseline exists

- AC-3: debug.json sha256 comparison is pending until SA-1 baseline exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: debug.json sha256 comparison is pending until SA-1 baseline exists")
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md not yet created")
```

</details>

#### AC-3: baseline contains debug.json section when present

- AC-3: baseline contains debug.json section when present
   - Expected: has_json_section is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: baseline contains debug.json section when present")
if not rt_file_exists(baseline_path()):
    pending("SA-1 baseline gate — " + baseline_path() + " not yet created")
val baseline = read_file(baseline_path())
val has_json_section = baseline.contains("debug.json")
check_msg(has_json_section, "baseline missing debug.json section — SA-1 must record sidecar sha256")
expect(has_json_section).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md`
- **Design:** `doc/05_design/rtl_riscv_mdsoc_capsules.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `41873616ebb9210a58fb9c2cb0b75e1808072d6b0c2de20b20fb07d07856b9b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `41873616ebb9210a58fb9c2cb0b75e1808072d6b0c2de20b20fb07d07856b9b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `41873616ebb9210a58fb9c2cb0b75e1808072d6b0c2de20b20fb07d07856b9b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/system/compiler/debug_sidecar_json_order_spec.spl
mirror: doc/06_spec/system/compiler/debug_sidecar_json_order_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/system/compiler/debug_sidecar_json_order_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/compiler/debug_sidecar_json_order_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/compiler/debug_sidecar_json_order_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/system/compiler/debug_sidecar_json_order_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: fpga_linux_manifest.spl contains reportMarkers key string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/compiler/debug_sidecar_json_order_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: fpga_linux_manifest.spl contains runnerSuccessMarkers key string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/compiler/debug_sidecar_json_order_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: reportMarkers appears before runnerSuccessMarkers in manifest source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
