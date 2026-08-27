# Test Entry Numeric Guard Specification

> Tests covering test entry numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Entry Numeric Guard Specification

## Scenarios

### test entry numeric guard

#### guards malformed depth and limit values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards malformed depth and limit values
   - Expected: source does not contain `env_set("SIMPLE_TEST_DEPTH", (depth + 1).to_text())`
   - Expected: source does not contain `depth_str.to_int()`
   - Expected: source does not contain `env_set("SIMPLE_TEST_DEPTH", "\{depth + 1\}")`
   - Expected: source does not contain `arg[21:].to_int()`
   - Expected: source does not contain `arg[10:].to_int()`
   - Expected: source does not contain `arg[18:].to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards malformed depth and limit values")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = rt_file_read_text("src/app/cli/test_entry.spl") ?? ""

expect(source).to_contain("fn parse_test_entry_nonnegative_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("val depth = parse_test_entry_nonnegative_or_default(depth_str, 0)")
expect(source).to_contain("val depth = parse_test_entry_nonnegative_or_default(arg[21:], 0)")
expect(source).to_contain("val secs = parse_test_entry_nonnegative_or_default(arg[10:], 0)")
expect(source).to_contain("val limit = parse_test_entry_nonnegative_or_default(arg[18:], 0)")
expect(source).to_contain("env_set(\"SIMPLE_TEST_DEPTH\", \"1\")")
expect(source.contains("env_set(\"SIMPLE_TEST_DEPTH\", (depth + 1).to_text())")).to_equal(false)
expect(source.contains("depth_str.to_int()")).to_equal(false)
expect(source.contains("env_set(\"SIMPLE_TEST_DEPTH\", \"\{depth + 1\}\")")).to_equal(false)
expect(source.contains("arg[21:].to_int()")).to_equal(false)
expect(source.contains("arg[10:].to_int()")).to_equal(false)
expect(source.contains("arg[18:].to_int()")).to_equal(false)
```

</details>

#### keeps the lightweight test entry off the full CLI command hub

- keeps the lightweight test entry off the full CLI command hub
   - Expected: entry_source does not contain `extern fn rt_fault_`
   - Expected: entry_source does not contain `rt_fault_set_`
   - Expected: fault_source does not contain `use `
   - Expected: fault_source does not contain `timeout_ms`
   - Expected: entry_source does not contain `use app.io.cli_commands`
   - Expected: entry_source does not contain `use app.io._CliCommands.run_commands`
   - Expected: entry_source does not contain `use std.cli.cli_util`
   - Expected: entry_source does not contain `use app.io.mod`
   - Expected: run_source does not contain `use app.io.cli_commands.*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the lightweight test entry off the full CLI command hub")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val entry_source = rt_file_read_text("src/app/cli/test_entry.spl") ?? ""
val fault_source = rt_file_read_text("src/lib/nogc_sync_mut/sffi/fault.spl") ?? ""
val run_source = rt_file_read_text("src/app/io/_CliCommands/run_commands.spl") ?? ""

expect(entry_source).to_contain("use std.nogc_sync_mut.sffi.cli (cli_get_args, cli_run_tests)")
expect(entry_source).to_contain("use std.nogc_sync_mut.sffi.system (env_get, env_set)")
expect(entry_source).to_contain("use std.nogc_sync_mut.sffi.fault (fault_set_stack_overflow_detection, fault_set_max_recursion_depth, fault_set_timeout, fault_set_execution_limit)")
expect(entry_source.contains("extern fn rt_fault_")).to_equal(false)
expect(entry_source.contains("rt_fault_set_")).to_equal(false)
expect(entry_source).to_contain("fault_set_max_recursion_depth(depth)\n            fault_set_stack_overflow_detection(true)")
expect(entry_source).to_contain("val secs = parse_test_entry_nonnegative_or_default(arg[10:], 0)\n            fault_set_timeout(secs)")
expect(fault_source).to_contain("fn fault_set_stack_overflow_detection(enabled: bool):\n    rt_fault_set_stack_overflow_detection(enabled)")
expect(fault_source).to_contain("fn fault_set_max_recursion_depth(depth: i64):\n    rt_fault_set_max_recursion_depth(depth)")
expect(fault_source).to_contain("fn fault_set_timeout(secs: i64):\n    rt_fault_set_timeout(secs)")
expect(fault_source).to_contain("fn fault_set_execution_limit(limit: i64):\n    rt_fault_set_execution_limit(limit)")
expect(fault_source.contains("use ")).to_equal(false)
expect(fault_source.contains("timeout_ms")).to_equal(false)
expect(entry_source.contains("use app.io.cli_commands")).to_equal(false)
expect(entry_source.contains("use app.io._CliCommands.run_commands")).to_equal(false)
expect(entry_source.contains("use std.cli.cli_util")).to_equal(false)
expect(entry_source.contains("use app.io.mod")).to_equal(false)
expect(run_source.contains("use app.io.cli_commands.*")).to_equal(false)
expect(run_source).to_contain("use compiler.common.driver_core_types.\{CompileResult\}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/test_entry_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test entry numeric guard.
- test entry numeric guard

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `47387ff0ad9a0957034a5176b1cd4ffc8beb79b778b798137c4e5ce1eb19008a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47387ff0ad9a0957034a5176b1cd4ffc8beb79b778b798137c4e5ce1eb19008a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47387ff0ad9a0957034a5176b1cd4ffc8beb79b778b798137c4e5ce1eb19008a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli/test_entry_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/cli/test_entry_numeric_guard_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli/test_entry_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/test_entry_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/test_entry_numeric_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
