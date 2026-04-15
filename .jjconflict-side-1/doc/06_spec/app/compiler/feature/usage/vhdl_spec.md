# VHDL Backend Toolchain

Tests VHDL backend toolchain integration with GHDL and Yosys. Covers GHDL availability detection, VHDL source analysis (valid and invalid files), entity elaboration, simulation with stop time, synthesis, file I/O operations (write, read, exists), VhdlToolResult structure validation, and Yosys integration via the GHDL plugin for synthesis to JSON netlist.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/vhdl_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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
VHDL Backend Feature Tests

Tests specific to VHDL backend toolchain functionality.
Tests GHDL and Yosys availability and wrapper functions.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/vhdl/result.json` |

## Scenarios

- checks GHDL availability
- checks Yosys availability
- analyzes valid VHDL file
- rejects invalid VHDL file
- elaborates valid entity
- runs simulation with stop time
- synthesizes a simple entity
- writes and reads VHDL file
- returns nil for non-existent file
- checks file existence
- has correct fields on success
- synthesizes VHDL via Yosys+GHDL plugin
