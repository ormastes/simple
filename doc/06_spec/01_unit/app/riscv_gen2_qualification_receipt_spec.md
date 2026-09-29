# Riscv Gen2 Qualification Receipt Specification

> Tests covering RISC-V Gen2 qualification receipt contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Gen2 Qualification Receipt Specification

## Scenarios

### RISC-V Gen2 qualification receipt contract

#### should accept the fixed RV32 and RV64 measured branch manifest

- should accept the fixed RV32 and RV64 measured branch manifest
- Parse the exact v2 two-row qualification manifest
   - Expected: manifest.rows.len() equals `2`
   - Expected: manifest.rows[0].architecture equals `rv32`
   - Expected: manifest.rows[1].architecture equals `rv64`
   - Expected: manifest.rows[0].target equals `rv32-zca-cjal-critical`
   - Expected: manifest.branch_coverage_basis_points equals `8000`
   - Expected: manifest.changed_files.len() equals `2`
   - Expected: manifest.exclusions.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should accept the fixed RV32 and RV64 measured branch manifest")
step("Parse the exact v2 two-row qualification manifest")
val parsed = riscv_gen2_parse_qualification_manifest(_manifest())
expect(parsed.is_ok()).to_be(true)
val manifest = parsed.unwrap()
expect(manifest.rows.len()).to_equal(2)
expect(manifest.rows[0].architecture).to_equal("rv32")
expect(manifest.rows[1].architecture).to_equal("rv64")
expect(manifest.rows[0].target).to_equal("rv32-zca-cjal-critical")
expect(manifest.rows[1].profile).to_equal(
    "riscv-gen2-rv64-zca-addiw-critical")
expect(manifest.branch_coverage_basis_points).to_equal(8000)
expect(manifest.owned_file_list_sha256).to_equal(
    _owned_file_list_sha256())
expect(manifest.owned_file_manifest_path).to_equal(
    "evidence/owned-files.list")
expect(manifest.changed_files.len()).to_equal(2)
expect(manifest.exclusions.len()).to_equal(4)
```

</details>

#### should reject missing rows, nonzero exits, and subcanonical branch coverage

- should reject missing rows, nonzero exits, and subcanonical branch coverage
- Reject incomplete rows, failed product commands, swapped targets, and low coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject missing rows, nonzero exits, and subcanonical branch coverage")
step("Reject incomplete rows, failed product commands, swapped targets, and low coverage")
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("row_2_architecture=rv64\n", "")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("row_1_product_exit_code=0",
        "row_1_product_exit_code=1")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("row_2_target=rv64-zca-addiw-critical",
        "row_2_target=rv32-zca-cjal-critical")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("branch_coverage_basis_points=8000",
        "branch_coverage_basis_points=7999")
).is_err()).to_be(true)
```

</details>

#### should reject incomplete command, testbench, coverage, and list bindings

- should reject incomplete command, testbench, coverage, and list bindings
- Reject missing or duplicate command, testbench, coverage, and list bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject incomplete command, testbench, coverage, and list bindings")
step("Reject missing or duplicate command, testbench, coverage, and list bindings")
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("row_1_testbench_sha256={_HASH}\n", "")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("row_2_analyze_exit_code=0",
        "row_2_analyze_exit_code=1")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("branch_coverage_command_sha256={_HASH}",
        "branch_coverage_command_sha256=bad")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("changed_file_count=2", "changed_file_count=0")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace("exclusion_2=generated VHDL testbench literals",
        "exclusion_2=generated VHDL artifacts")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest() + "row_1_run_exit_code=0\n"
).is_err()).to_be(true)
```

</details>

#### should reject missing, malformed, duplicate, or mismatched owned file list identity

- should reject missing, malformed, duplicate, or mismatched owned file list identity
- Bind the exact newline-terminated owned file list into one v2 digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject missing, malformed, duplicate, or mismatched owned file list identity")
step("Bind the exact newline-terminated owned file list into one v2 digest")
val owned_line = "owned_file_list_sha256={_owned_file_list_sha256()}\n"
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace(owned_line, "")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace(_owned_file_list_sha256(), "bad")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest() + owned_line
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace(_owned_file_list_sha256(), "b" * 64)
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace(
        "owned_file_manifest_path=evidence/owned-files.list\n", "")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest().replace(
        "owned_file_manifest_sha256={_HASH}",
        "owned_file_manifest_sha256=bad")
).is_err()).to_be(true)
expect(riscv_gen2_parse_qualification_manifest(
    _manifest() +
        "owned_file_manifest_path=evidence/owned-files.list\n"
).is_err()).to_be(true)
```

</details>

#### should bind canonical owned hash rows to ordered changed files and current source

- should bind canonical owned hash rows to ordered changed files and current source
- Require 64hex two-space path rows with current file hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should bind canonical owned hash rows to ordered changed files and current source")
step("Require 64hex two-space path rows with current file hashes")
val paths = [
    "src/app/test/riscv_gen2_qualification_receipt.spl",
    "test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl"]
val rows = file_hash_sha256(paths[0]) + "  " + paths[0] + "\n" +
    file_hash_sha256(paths[1]) + "  " + paths[1] + "\n"
expect(riscv_gen2_owned_file_manifest_matches(rows, paths)).to_be(true)
expect(riscv_gen2_owned_file_manifest_matches(
    rows.replace(file_hash_sha256(paths[0]), "b" * 64), paths
)).to_be(false)
expect(riscv_gen2_owned_file_manifest_matches(
    rows.replace("  " + paths[0], " " + paths[0]), paths
)).to_be(false)
expect(riscv_gen2_owned_file_manifest_matches(
    rows, [paths[1], paths[0]])).to_be(false)
```

</details>

#### should render only bound command and retained evidence identities

- should render only bound command and retained evidence identities
- Render the nested receipt from validated v2 identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should render only bound command and retained evidence identities")
step("Render the nested receipt from validated v2 identities")
val manifest = riscv_gen2_parse_qualification_manifest(_manifest()).unwrap()
val rendered = riscv_gen2_render_qualification_receipt(
    manifest, "qualified-run-001", _HASH)
expect(rendered).to_contain("\"schema\":\"" +
    RISCV_GEN2_QUALIFICATION_SCHEMA + "\"")
expect(rendered).to_contain("\"threshold_basis_points\":8000")
expect(rendered).to_contain("\"architecture\":\"rv32\"")
expect(rendered).to_contain("\"architecture\":\"rv64\"")
expect(rendered).to_contain(
    "\"product_id\":\"riscv-gen2-zca-trap-single-outstanding-v3\"")
expect(rendered).to_contain(
    "\"retained_path\":\"rv32.manifest.json\"")
expect(rendered).to_contain("\"product_exit_code\":0")
expect(rendered).to_contain("\"retained_path\":\"rv32.tb.vhd\"")
expect(rendered).to_contain("\"retained_path\":\"rv64.run.command\"")
expect(rendered).to_contain("\"changed_files\":[")
expect(rendered).to_contain(
    "\"owned_file_list_sha256\":\"{_owned_file_list_sha256()}\"")
expect(rendered).to_contain(
    "\"retained_path\":\"owned-files.list\"")
expect(rendered).to_contain("\"exclusions\":[")
```

</details>

#### should reject duplicate or mismatched product-manifest authority

- should reject duplicate or mismatched product-manifest authority
- Bind the producer JSON structurally and reject duplicate authority keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject duplicate or mismatched product-manifest authority")
step("Bind the producer JSON structurally and reject duplicate authority keys")
val row = riscv_gen2_parse_qualification_manifest(_manifest()).unwrap().rows[0]
val product_manifest = "{" +
    "\"entry_entity\":\"riscv_gen2_zca_rv32_cjal_trap_single_outstanding_frontend\"," +
    "\"source_closure_sha256\":\"{_HASH}\"," +
    "\"vhdl\":{\"path\":\"{cwd()}/evidence/rv32.vhd\",\"sha256\":\"{_HASH}\"}," +
    "\"generation_route\":\"hwir-gen2-trap-stateful-product-v3\"," +
    "\"hwir\":{\"config_profile\":\"riscv-gen2-rv32-zca-cjal-critical\",\"graph_sha256\":\"{_HASH}\"}," +
    "\"assurance_policy\":{\"strictness\":\"critical\"}," +
    "\"target\":{\"name\":\"riscv32\",\"xlen\":32,\"profile\":\"riscv-gen2-rv32-zca-cjal-critical\"}}"
expect(riscv_gen2_qualification_product_manifest_matches(
    product_manifest, row)).to_be(true)
expect(riscv_gen2_qualification_product_manifest_matches(
    "{\"entry_entity\":\"shadow\"," + product_manifest[1:],
    row)).to_be(false)
expect(riscv_gen2_qualification_product_manifest_matches(
    product_manifest.replace("\"graph_sha256\":\"{_HASH}\"",
        "\"graph_sha256\":\"" + ("b" * 64) + "\""), row)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V Gen2 qualification receipt contract.
- RISC-V Gen2 qualification receipt contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-G2-004`
- `REQ-G2-006`
- `REQ-G2-009`
- `REQ-G2-010`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `03852167f438ef4803d59e58f0a466758937e6afae8aae25a975ab3d757a2c63`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03852167f438ef4803d59e58f0a466758937e6afae8aae25a975ab3d757a2c63`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03852167f438ef4803d59e58f0a466758937e6afae8aae25a975ab3d757a2c63`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl
mirror: doc/06_spec/01_unit/app/riscv_gen2_qualification_receipt_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/riscv_gen2_qualification_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/riscv_gen2_qualification_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept the fixed RV32 and RV64 measured branch manifest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept the fixed RV32 and RV64 measured branch manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:118:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing rows, nonzero exits, and subcanonical branch coverage' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing rows, nonzero exits, and subcanonical branch coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:138:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject incomplete command, testbench, coverage, and list bindings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject incomplete command, testbench, coverage, and list bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing, malformed, duplicate, or mismatched owned file list identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:194:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind canonical owned hash rows to ordered changed files and current source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl:213:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render only bound command and retained evidence identities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
