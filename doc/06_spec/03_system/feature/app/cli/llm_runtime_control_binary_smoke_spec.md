# LLM Runtime Control Release Binary Smoke Specification

> This system smoke test proves the tracked release Simple binary ships the top-level `llm-runtime-control` app command. It guards against the stale-artifact failure mode where the release binary treats the command name as a source file.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Runtime Control Release Binary Smoke Specification

This system smoke test proves the tracked release Simple binary ships the top-level `llm-runtime-control` app command. It guards against the stale-artifact failure mode where the release binary treats the command name as a source file.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LLM-RUNTIME-CONTROL-BINARY-001 |
| Category | App CLI |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md |
| Plan | doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md |
| Design | doc/05_design/app/llm_runtime_vllm_torch_interface.md |
| Source | `test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system smoke test proves the tracked release Simple binary ships the
top-level `llm-runtime-control` app command. It guards against the stale-artifact
failure mode where the release binary treats the command name as a source file.

## Scenarios

### llm-runtime-control release binary dispatch

#### ships a release binary with llm-runtime-control dispatch

- ships a release binary with llm-runtime-control dispatch
   - Expected: file_exists(RELEASE_SIMPLE) is true
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ships a release binary with llm-runtime-control dispatch")
expect(file_exists(RELEASE_SIMPLE)).to_equal(true)

val (output, exit_code) = run_release_control([
    "--action", "preflight",
    "--base-model", "base-model",
    "--endpoint", "http://127.0.0.1:8000/v1"
])

expect(exit_code).to_equal(0)
expect(output).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(output).to_contain("\"action\":\"preflight\"")
expect(output).to_contain("\"status\":\"skipped\"")
expect(output).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(output).to_contain("\"models_reason\":\"environment_skipped\"")
expect_text_absent(output, "file not found: llm-runtime-control")
expect_text_absent(output, "base-model")
expect_absence_marker_hidden(output)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md`
- **Plan:** `doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md`
- **Design:** `doc/05_design/app/llm_runtime_vllm_torch_interface.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-RUNTIME-CONTROL-BINARY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ce16ddaf2c564cae29cd3f7f671ac9db1c54aeb3d83c945ef6abe8f4480dc9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ce16ddaf2c564cae29cd3f7f671ac9db1c54aeb3d83c945ef6abe8f4480dc9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ce16ddaf2c564cae29cd3f7f671ac9db1c54aeb3d83c945ef6abe8f4480dc9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl
mirror: doc/06_spec/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships a release binary with llm-runtime-control dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
