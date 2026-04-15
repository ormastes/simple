# Ghdl Riscv32 Mailbox Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/ghdl_riscv32_mailbox_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 9 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/ghdl_riscv32_mailbox/result.json` |

## Scenarios

- runner script exists and is syntax-valid
- capability probe returns mailbox lane_id
- adapter creates with default configuration
- adapter capability report has correct lane_id
- adapter rejects execute without elf
- adapter set_elf stores path
- adapter set_timeout stores value
- [slow] adapter executes hello mailbox ELF
- [slow] prints hello mailbox message
- [slow] reports exit code 0 via sentinel
- [slow] reports SENTINEL marker in output
- [slow] reports result value from CMD_RESULT
- [slow] rejects missing ELF path
- [slow] handles timeout gracefully
- [slow] does not depend on semihost output
- [slow] mailbox output is distinct from semihost lane
