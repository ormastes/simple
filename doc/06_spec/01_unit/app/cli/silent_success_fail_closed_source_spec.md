# Silent Success Fail Closed Source Specification

> Tests covering CLI silent-success fail-closed invariants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Silent Success Fail Closed Source Specification

## Scenarios

### CLI silent-success fail-closed invariants

#### rejects a native-build worker that exits 0 without an output binary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a native-build worker that exits 0 without an output binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a native-build worker that exits 0 without an output binary")
val source = src("src/app/cli/native_build_main.spl")
expect(source.len()).to_be_greater_than(0)
expect(source).to_contain("if code == 0 and output_path != \"\" and not rt_file_exists(output_path):")
expect(source).to_contain("error: native-build worker exited 0 but produced no output binary")
```

</details>

#### rejects a compiler driver Success that wrote no artifact

- rejects a compiler driver Success that wrote no artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a compiler driver Success that wrote no artifact")
val source = src("src/app/io/_CliCompile/compile_targets.spl")
expect(source.len()).to_be_greater_than(0)
# The staged sibling is what makes the check meaningful: without it a
# STALE requested output would satisfy the success test.
expect(source).to_contain(".simple-native-build-")
expect(source).to_contain("error: native-build reported success but produced no fresh output binary")
```

</details>

#### reads argv through the runtime extern, never through a same-named import

- reads argv through the runtime extern, never through a same-named import
   - Expected: source does not contain `use std.io_runtime`
   - Expected: source does not contain `use std.nogc_sync_mut.io_runtime`
   - Expected: source does not contain `use nogc_sync_mut.io_runtime`
   - Expected: source does not contain `use io_runtime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reads argv through the runtime extern, never through a same-named import")
# `fn get_args()` importing `get_args` from std.io_runtime bound the call
# to itself and recursed until the stack died (Stage 4 SIGSEGV on every
# invocation, including `print(1)`). The wrapper must call the extern.
val source = src("src/app/io/cli_ops.spl")
expect(source.len()).to_be_greater_than(0)
expect(source).to_contain("extern fn rt_cli_get_args() -> [text]")
expect(source).to_contain("extern fn rt_exit(code: i64)")
expect(source).to_contain("rt_cli_get_args()")
# Re-importing either name here reintroduces the self-binding recursion.
# All four spellings are blocked, not just the two `std.`-prefixed ones:
# `use nogc_sync_mut.io_runtime.{get_args}` resolves to the same module
# and would reintroduce the defect while passing a `std.`-only guard.
expect(source.contains("use std.io_runtime")).to_equal(false)
expect(source.contains("use std.nogc_sync_mut.io_runtime")).to_equal(false)
expect(source.contains("use nogc_sync_mut.io_runtime")).to_equal(false)
expect(source.contains("use io_runtime")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI silent-success fail-closed invariants.
- CLI silent-success fail-closed invariants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f54f7c1a152c149dde5c75e08b7f42e2f5c25bbbcd0c8f52561e884360d4e8ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f54f7c1a152c149dde5c75e08b7f42e2f5c25bbbcd0c8f52561e884360d4e8ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f54f7c1a152c149dde5c75e08b7f42e2f5c25bbbcd0c8f52561e884360d4e8ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl
mirror: doc/06_spec/01_unit/app/cli/silent_success_fail_closed_source_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli/silent_success_fail_closed_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/silent_success_fail_closed_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a native-build worker that exits 0 without an output binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a compiler driver Success that wrote no artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads argv through the runtime extern, never through a same-named import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
