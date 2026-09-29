# Generate Rv64 Test Program Package Specification

> Tests covering generate_rv64_test_program_package.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generate Rv64 Test Program Package Specification

## Scenarios

### generate_rv64_test_program_package

#### emits 64-bit preload rows and keeps byte-array metadata coherent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits 64-bit preload rows and keeps byte-array metadata coherent
   - Expected: shell("rm -rf '" + root + "' && mkdir -p '" + root + "'") equals `0`
   - Expected: shell("printf '\\001\\002\\003\\004\\005\\006\\007\\010\\011' > '" + fw_bin + "'") equals `0`
   - Expected: shell("printf '\\252\\273\\314\\335' > '" + payload_bin + "'") equals `0`
   - Expected: shell("bin/simple run src/hardware/fpga_linux/generate_rv64_test_program_package.spl -- '" + fw_bin + "' '" + fw_hex + "' '" + payload_bin + "' '" + payload_hex + "' '" + pkg + "'") equals `0`
   - Expected: file_read(fw_hex) equals `0807060504030201\n0000000000000009\n`
   - Expected: file_read(payload_hex) equals `00000000DDCCBBAA\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 64-bit preload rows and keeps byte-array metadata coherent")
val root = "/tmp/generate_rv64_test_program_package_spec"
val fw_bin = "{root}/fw.bin"
val fw_hex = "{root}/fw.hex"
val payload_bin = "{root}/payload.bin"
val payload_hex = "{root}/payload.hex"
val pkg = "{root}/test_program.vhd"

expect(shell("rm -rf '" + root + "' && mkdir -p '" + root + "'")).to_equal(0)

expect(shell("printf '\\001\\002\\003\\004\\005\\006\\007\\010\\011' > '" + fw_bin + "'")).to_equal(0)
expect(shell("printf '\\252\\273\\314\\335' > '" + payload_bin + "'")).to_equal(0)

expect(shell("bin/simple run src/hardware/fpga_linux/generate_rv64_test_program_package.spl -- '" + fw_bin + "' '" + fw_hex + "' '" + payload_bin + "' '" + payload_hex + "' '" + pkg + "'")).to_equal(0)

expect(file_read(fw_hex)).to_equal("0807060504030201\n0000000000000009\n")
expect(file_read(payload_hex)).to_equal("00000000DDCCBBAA\n")

val pkg_text = file_read(pkg)
expect(pkg_text).to_contain("constant HEX_WORD_BYTES : integer := 8;")
expect(pkg_text).to_contain("constant FW_SIZE_BYTES : integer := 9;")
expect(pkg_text).to_contain("constant FW_HEX_PATH : string := \"" + fw_hex + "\";")
expect(pkg_text).to_contain("constant PAYLOAD_SIZE_BYTES : integer := 4;")
expect(pkg_text).to_contain("constant PAYLOAD_HEX_PATH : string := \"" + payload_hex + "\";")
expect(pkg_text).to_contain("constant FW_BYTES : byte_array_t(0 to 8) := (")
expect(pkg_text).to_contain("        x\"01\",")
expect(pkg_text).to_contain("        x\"09\"\n    );")
expect(pkg_text).to_contain("constant PAYLOAD_BYTES : byte_array_t(0 to 3) := (")
expect(pkg_text).to_contain("        x\"AA\",")
expect(pkg_text).to_contain("        x\"DD\"\n    );")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering generate_rv64_test_program_package.
- generate_rv64_test_program_package

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `2c7528dbb9f074cfbf52c53cc8084d2d509c1a7acbcc8cea617c0bc5fb594743`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c7528dbb9f074cfbf52c53cc8084d2d509c1a7acbcc8cea617c0bc5fb594743`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c7528dbb9f074cfbf52c53cc8084d2d509c1a7acbcc8cea617c0bc5fb594743`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl
mirror: doc/06_spec/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 64-bit preload rows and keeps byte-array metadata coherent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
