# VHDL Backend Toolchain

**Feature ID:** #VHDL-002 | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/usage/vhdl_spec.spl`_

---

## Overview

Tests VHDL backend toolchain integration with GHDL and Yosys. Covers GHDL
availability detection, VHDL source analysis (valid and invalid files),
entity elaboration, simulation with stop time, synthesis, file I/O operations
(write, read, exists), VhdlToolResult structure validation, and Yosys
integration via the GHDL plugin for synthesis to JSON netlist.

## Syntax

```simple
val result = ghdl_analyze(path)
expect(result.exit_code).to_equal(0)
val content = vhdl_read_file(path)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 12 |

## Test Structure

### VHDL Toolchain Availability

- ✅ checks GHDL availability
- ✅ checks Yosys availability
### GHDL Analysis

- ✅ analyzes valid VHDL file
- ✅ rejects invalid VHDL file
### GHDL Elaboration

- ✅ elaborates valid entity
### GHDL Simulation

- ✅ runs simulation with stop time
### GHDL Synthesis

- ✅ synthesizes a simple entity
### VHDL File Operations

- ✅ writes and reads VHDL file
- ✅ returns nil for non-existent file
- ✅ checks file existence
### VhdlToolResult structure

- ✅ has correct fields on success
### Yosys VHDL Synthesis

- ✅ synthesizes VHDL via Yosys+GHDL plugin

