# Riscv Product Ports Source Specification

> Tests covering RISC-V product scalar ports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Product Ports Source Specification

## Scenarios

### RISC-V product scalar ports

#### keeps RV32 platform sampling ahead of the protected cycle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps RV32 platform sampling ahead of the protected cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps RV32 platform sampling ahead of the protected cycle")
val path = "src/lib/hardware/rv32i_rtl/protected_entry.spl"
val source = file_read_text(path)
expect_flat_product_ports(path, ["bus_valid", "bus_addr", "bus_size",
    "bus_write", "bus_wdata", "bus_is_pte", "bus_atomic", "bus_lock"])
expect(source).to_contain("msip: bool, mtip: bool, meip: bool")
expect(source).to_contain("stip: bool, seip: bool, time_value: i64")
expect(source).to_contain("response_data: u32) -> Core32ProductPorts")
expect(source).to_contain("@flatten_struct_output")
expect(source).to_contain("rvfi_mode: u32 @bits(2)")
expect(source).to_contain("rvfi_rs1_addr: u32 @bits(5)")
expect(source).to_contain("rvfi_mem_rmask: u32 @bits(4)")
expect(source).to_contain("core32_set_pending_interrupts(_core32_product_state")
expect(source).to_contain("core32_set_supervisor_pending_interrupts(sampled")
expect(source).to_contain("core32_set_time_value(sampled, time_value)")
expect(source.index_of("core32_set_time_value(sampled, time_value)")).to_be_less_than(
    source.index_of("core32_cycle(sampled"))
```

</details>

#### keeps RV64IMAC memory images and DTB outside the CPU ABI

- keeps RV64IMAC memory images and DTB outside the CPU ABI
   - Expected: source does not contain `dtb:`
   - Expected: source does not contain `mem_image`
   - Expected: source does not contain `memory_image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps RV64IMAC memory images and DTB outside the CPU ABI")
val path = "src/lib/hardware/rv64gc_rtl/imac_entry.spl"
val source = file_read_text(path)
expect_flat_product_ports(path, ["bus_valid", "bus_addr", "bus_size",
    "bus_write", "bus_wdata", "bus_is_pte", "bus_atomic"])
expect(source).to_contain("response_data: i64) -> Core64ImacProductPorts")
expect(source).to_contain("@flatten_struct_output")
expect(source).to_contain("rvfi_mode: u32 @bits(2)")
expect(source).to_contain("rvfi_rs1_addr: u32 @bits(5)")
expect(source).to_contain("rvfi_mem_rmask: u32 @bits(8)")
expect(source).to_contain("struct Core64ImacProductPorts:")
# DTB bytes and memory images belong to the SoC memory owner, not this
# CPU port: prove that by the ports struct carrying no such field.
expect(source.contains("dtb:")).to_equal(false)
expect(source.contains("mem_image")).to_equal(false)
expect(source.contains("memory_image")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V product scalar ports.
- RISC-V product scalar ports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a54f7eb2bc37165bc1fc376a40e8c694f23d00072cf422b212d469d4771211d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a54f7eb2bc37165bc1fc376a40e8c694f23d00072cf422b212d469d4771211d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a54f7eb2bc37165bc1fc376a40e8c694f23d00072cf422b212d469d4771211d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/riscv_product_ports_source_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/lib/hardware/riscv_product_ports_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/riscv_product_ports_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RV32 platform sampling ahead of the protected cycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RV64IMAC memory images and DTB outside the CPU ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
