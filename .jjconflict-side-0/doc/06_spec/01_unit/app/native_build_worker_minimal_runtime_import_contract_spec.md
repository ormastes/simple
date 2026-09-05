# Native Build Worker Minimal Runtime Import Contract Specification

> Tests covering native-build worker minimal runtime imports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Worker Minimal Runtime Import Contract Specification

## Scenarios

### native-build worker minimal runtime imports

#### does not pull the general CLI facade into the compiler closure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not pull the general CLI facade into the compiler closure
   - Expected: source does not contain `use app.io.cli_ops`
   - Expected: source does not contain `extern fn rt_cli_get_args`
   - Expected: source does not contain `extern fn sys_get_args`
   - Expected: source does not contain `extern fn rt_env_get`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not pull the general CLI facade into the compiler closure")
val source = file_read("src/app/cli/native_build_worker.spl")

expect(source.contains("use app.io.cli_ops")).to_equal(false)
expect(source).to_contain('use app.io.args_ops.{get_args}')
expect(source).to_contain('use app.io.env_ops.{env_get}')
expect(source.contains("extern fn rt_cli_get_args")).to_equal(false)
expect(source.contains("extern fn sys_get_args")).to_equal(false)
expect(source).to_contain("val raw_args = get_args()")
expect(source).to_contain('env_get("SIMPLE_NATIVE_BUILD_WORKER")')
expect(source.contains("extern fn rt_env_get")).to_equal(false)
expect(source).to_contain("rt_exit(1)")
expect(source).to_contain("cli_native_build(native_build_entry_args())")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build worker minimal runtime imports.
- native-build worker minimal runtime imports

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f184d4b77a7efb70271f219707e3169e5c90cf54381b4d9b36bbb70241b843d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f184d4b77a7efb70271f219707e3169e5c90cf54381b4d9b36bbb70241b843d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f184d4b77a7efb70271f219707e3169e5c90cf54381b4d9b36bbb70241b843d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.spl
mirror: doc/06_spec/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not pull the general CLI facade into the compiler closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
