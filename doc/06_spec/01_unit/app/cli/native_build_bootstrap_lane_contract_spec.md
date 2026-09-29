# Native Build Bootstrap Lane Contract Specification

> Tests covering native-build / bootstrap CLI entry source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Bootstrap Lane Contract Specification

## Scenarios

### native-build / bootstrap CLI entry source contract

#### never injects an execution mode into the worker argv

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- never injects an execution mode into the worker argv
   - Expected: src does not contain `--mode=interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never injects an execution mode into the worker argv")
## baremetal_entry_closure_class_instantiation_fault_2026-07-06 recorded
## that run_native_build_worker appended `--mode=interpreter` to the
## worker argv, which the worker's own parser then rejected. The mode is
## now carried by the SIMPLE_EXECUTION_MODE environment variable only.
val src = file_read("src/app/cli/native_build_main.spl")
expect(src.contains("--mode=interpreter")).to_equal(false)
expect(src).to_contain("env_set(\"SIMPLE_EXECUTION_MODE\", \"interpret\")")
```

</details>

#### keeps the rerun-diagnostics hint reachable from a failing worker

- keeps the rerun-diagnostics hint reachable from a failing worker


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the rerun-diagnostics hint reachable from a failing worker")
## bootstrap_logging_diagnostics_2026-07-07: a nil `.id` failure must
## tell the operator which env vars re-run it with phase/function names.
val src = file_read("src/app/cli/native_build_main.spl")
expect(src).to_contain("SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1")
expect(src).to_contain("undefined field 'id'")
expect(src).to_contain("native_build_print_failure_hints(stdout, stderr)")
```

</details>

#### preserves diagnostics across stderr truncation

- preserves diagnostics across stderr truncation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves diagnostics across stderr truncation")
## A head+tail truncation drops the middle, so a `grep -c` over the
## relayed stderr can report 0 for a diagnostic that actually fired.
## Every diagnostic line from the FULL stream must be re-emitted.
val src = file_read("src/app/cli/native_build_main.spl")
expect(src).to_contain("fn native_build_collect_diagnostics(output: text) -> [text]:")
expect(src).to_contain("BEGIN PRESERVED DIAGNOSTICS")
expect(src).to_contain("NATIVE-BUILD STDERR TRUNCATED")
```

</details>

#### treats a zero exit with no output binary as a hard failure

- treats a zero exit with no output binary as a hard failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a zero exit with no output binary as a hard failure")
## The silent-wrong-result shape for this lane: worker chain dies in a
## way that still exits 0 and the caller proceeds with a stale binary.
val src = file_read("src/app/cli/native_build_main.spl")
expect(src).to_contain("exited 0 but produced no output binary")
```

</details>

#### never reports in-process native-build success without a real artifact

- never reports in-process native-build success without a real artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never reports in-process native-build success without a real artifact")
## bootstrap_main's compile() could fall through with no mode matched,
## return Success, emit nothing, and exit 0. Both in-process lanes must
## assert the artifact exists AND is not a stub.
val src = file_read("src/app/cli/bootstrap_main.spl")
expect(src).to_contain("error: in-process native-build reported success without creating")
expect(src).to_contain("error: in-process native-build produced a stub artifact")
expect(src).to_contain("error: in-process SMF compile reported success without creating")
expect(src).to_contain("error: in-process SMF compile produced a stub artifact")
```

</details>

#### keeps the cli_mode_text override on both in-process compile lanes

- keeps the cli_mode_text override on both in-process compile lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the cli_mode_text override on both in-process compile lanes")
## The enum `options.mode` does not survive struct transport into a
## COMPILED stage2 driver; cli_mode_text is what makes the lane work.
val src = file_read("src/app/cli/bootstrap_main.spl")
expect(src).to_contain("options.cli_mode_text = \"aot\"")
```

</details>

#### keeps bootstrap_main free of seed-wrapper artifact generation

- keeps bootstrap_main free of seed-wrapper artifact generation
   - Expected: seed_wrapper_marker(src) equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bootstrap_main free of seed-wrapper artifact generation")
val src = file_read("src/app/cli/bootstrap_main.spl")
expect(seed_wrapper_marker(src)).to_equal("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build / bootstrap CLI entry source contract.
- native-build / bootstrap CLI entry source contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `13b33d021112df1fd4a134b9ca685762abb59c8704b1aef206bdbb64bae6c139`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13b33d021112df1fd4a134b9ca685762abb59c8704b1aef206bdbb64bae6c139`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13b33d021112df1fd4a134b9ca685762abb59c8704b1aef206bdbb64bae6c139`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl
mirror: doc/06_spec/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never injects an execution mode into the worker argv' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the rerun-diagnostics hint reachable from a failing worker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves diagnostics across stderr truncation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
