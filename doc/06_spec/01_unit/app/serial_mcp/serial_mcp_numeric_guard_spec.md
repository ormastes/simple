# Serial Mcp Numeric Guard Specification

> Tests covering serial mcp numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Mcp Numeric Guard Specification

## Scenarios

### serial mcp numeric guard

#### defaults malformed integer arguments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults malformed integer arguments
   - Expected: get_arg_int(args, "baud", 115200) equals `9600`
   - Expected: get_arg(args, "device") equals `/dev/ttyUSB0`
   - Expected: get_arg_int(args, "missing", 115200) equals `115200`
   - Expected: get_arg_int("{\"baud\": \"fast\"}", "baud", 115200) equals `115200`
   - Expected: get_arg_int("{\"baud\": \"\"}", "baud", 115200) equals `115200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults malformed integer arguments")
val args = "{\"device\": \"/dev/ttyUSB0\", \"baud\": \"9600\"}"
# oracle: present numeric field parses to its integer value
expect(get_arg_int(args, "baud", 115200)).to_equal(9600)
expect(get_arg(args, "device")).to_equal("/dev/ttyUSB0")
# oracle: absent field falls back to the caller default
expect(get_arg_int(args, "missing", 115200)).to_equal(115200)
# oracle: non-numeric field value falls back to the caller default
expect(get_arg_int("{\"baud\": \"fast\"}", "baud", 115200)).to_equal(115200)
expect(get_arg_int("{\"baud\": \"\"}", "baud", 115200)).to_equal(115200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering serial mcp numeric guard.
- serial mcp numeric guard

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `528ec7095eb682fcb6f05752a11144aecc8fdc227b6401b042099831916ae824`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `528ec7095eb682fcb6f05752a11144aecc8fdc227b6401b042099831916ae824`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `528ec7095eb682fcb6f05752a11144aecc8fdc227b6401b042099831916ae824`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults malformed integer arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
