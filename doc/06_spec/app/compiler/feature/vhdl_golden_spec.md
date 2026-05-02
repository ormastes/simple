# VHDL Golden File Tests

**Feature ID:** #VHDL-001 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/vhdl_golden_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 5 |

## Test Structure

### VHDL Golden File Tests

- ✅ counter matches golden reference
- ✅ ALU matches golden reference
- ✅ golden files exist on disk
### VHDL Golden Output Sanity

- ✅ counter output has required VHDL structure
- ✅ ALU output has required VHDL structure

