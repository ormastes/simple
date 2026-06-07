# RISC-V FPGA Bug Tracking Convention Specification

> Verifies AC-7: the bug tracking convention for RISC-V FPGA bugs uses the correct ID namespace (BUG-RISCV-FPGA-NNN) and that the bug-doc helper module generates conforming entry text.

<!-- sdn-diagram:id=riscv_fpga_bug_tracking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_fpga_bug_tracking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_fpga_bug_tracking_spec -> std
riscv_fpga_bug_tracking_spec -> doc
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_fpga_bug_tracking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V FPGA Bug Tracking Convention Specification

Verifies AC-7: the bug tracking convention for RISC-V FPGA bugs uses the correct ID namespace (BUG-RISCV-FPGA-NNN) and that the bug-doc helper module generates conforming entry text.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | Draft |
| Requirements | REQ-7 |
| Source | `test/01_unit/doc/riscv_fpga_bug_tracking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-7: the bug tracking convention for RISC-V FPGA bugs uses the
correct ID namespace (BUG-RISCV-FPGA-NNN) and that the bug-doc helper
module generates conforming entry text.

Per ADR D-7, bug entries are process artifacts (doc/bugs/). This spec
tests the convention module that generates bug entry templates, not
actual hardware bugs (which are filed during phase 7-verify).

Covers:
- AC-7 (Bug tracking: documented and fixed or tracked with concrete IDs)

## Scenarios

### RISC-V FPGA Bug Convention

#### AC-7: bug id prefix is BUG-RISCV-FPGA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = riscv_fpga_bug_id_prefix()
expect(prefix).to_equal("BUG-RISCV-FPGA")
```

</details>

#### AC-7: bug doc path starts with doc/bugs/

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = riscv_fpga_bug_doc_path(1)
expect(path).to_start_with("doc/bugs/")
```

</details>

#### AC-7: bug doc path contains BUG-RISCV-FPGA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = riscv_fpga_bug_doc_path(1)
expect(path).to_contain("BUG-RISCV-FPGA")
```

</details>

#### AC-7: bug doc path ends with .md

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = riscv_fpga_bug_doc_path(1)
expect(path).to_end_with(".md")
```

</details>

### RISC-V FPGA Bug Entry Template

#### AC-7: entry template is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = sample_entry_text()
val len = t.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-7: entry template contains BUG-RISCV-FPGA-001

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = sample_entry_text()
expect(t).to_contain("BUG-RISCV-FPGA-001")
```

</details>

#### AC-7: entry template contains the bug title

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = sample_entry_text()
expect(t).to_contain("UART output garbled on first boot")
```

</details>

#### AC-7: entry template contains status field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = sample_entry_text()
expect(t).to_contain("open")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-7](REQ-7)


</details>
