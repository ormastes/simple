# Generate Rv64 Test Program Package Specification

> <details>

<!-- sdn-diagram:id=generate_rv64_test_program_package_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generate_rv64_test_program_package_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generate_rv64_test_program_package_spec -> std
generate_rv64_test_program_package_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generate_rv64_test_program_package_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generate Rv64 Test Program Package Specification

## Scenarios

### generate_rv64_test_program_package

#### emits 64-bit preload rows and keeps byte-array metadata coherent

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
