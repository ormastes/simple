# VHDL Golden File Tests

Generates VHDL output from the VhdlBuilder and compares against checked-in reference .vhd golden files for regression testing. Validates counter and ALU entity generation including library headers, entity/architecture blocks, port declarations, signal assignments, clocked processes, and combinational logic. Also performs structural sanity checks on generated VHDL output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/feature/usage/vhdl_golden_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Generates VHDL output from the VhdlBuilder and compares against checked-in
reference .vhd golden files for regression testing. Validates counter and ALU
entity generation including library headers, entity/architecture blocks, port
declarations, signal assignments, clocked processes, and combinational logic.
Also performs structural sanity checks on generated VHDL output.

## Syntax

```simple
var builder = VhdlBuilder__create("counter")
builder.emit_library_header()
builder.emit_entity_begin("counter")
builder.emit_port("clk", "in", mapper.bit_type(), false)
val vhdl = builder.build()
```
VHDL Golden File Tests

Generates VHDL output from the builder and compares against
checked-in reference .vhd files in examples/09_embedded/vhdl/builder/golden/.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/vhdl_golden/result.json` |

## Scenarios

- counter matches golden reference
- ALU matches golden reference
- golden files exist on disk
- counter output has required VHDL structure
- ALU output has required VHDL structure
