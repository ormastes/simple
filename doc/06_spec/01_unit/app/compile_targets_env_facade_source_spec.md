# Compile Targets Env Facade Source Specification

> Tests covering compile-target environment facade source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Targets Env Facade Source Specification

## Scenarios

### compile-target environment facade source contract

#### routes both entry-closure trace flags through the environment facade

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes both entry-closure trace flags through the environment facade
   - Expected: source does not contain `rt_env_get`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes both entry-closure trace flags through the environment facade")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain("use app.io.env_ops (env_get, env_set)")
expect(source).to_contain('env_get("SIMPLE_NATIVE_BUILD_TRACE_CLOSURE")')
expect(source).to_contain('env_get("SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING")')
expect(source.contains("rt_env_get")).to_equal(false)
```

</details>

#### keeps adjacent native-build environment restoration on the same facade

- keeps adjacent native-build environment restoration on the same facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps adjacent native-build environment restoration on the same facade")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain('val old_log_mode = env_get("SIMPLE_OS_LOG_MODE") ?? ""')
expect(source).to_contain('val old_native_target = env_get("SIMPLE_NATIVE_BUILD_TARGET") ?? ""')
expect(source).to_contain('val old_runtime_path = env_get("SIMPLE_RUNTIME_PATH") ?? ""')
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/compile_targets_env_facade_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compile-target environment facade source contract.
- compile-target environment facade source contract

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

- Canonical SPipe generation for source `5d91c1dbbda66091538f2fcf8e22bb1b900d97998d0f917ff9dbc0d400312ec5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d91c1dbbda66091538f2fcf8e22bb1b900d97998d0f917ff9dbc0d400312ec5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d91c1dbbda66091538f2fcf8e22bb1b900d97998d0f917ff9dbc0d400312ec5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/compile_targets_env_facade_source_spec.spl
mirror: doc/06_spec/01_unit/app/compile_targets_env_facade_source_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/compile_targets_env_facade_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/compile_targets_env_facade_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/compile_targets_env_facade_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/compile_targets_env_facade_source_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes both entry-closure trace flags through the environment facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/compile_targets_env_facade_source_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps adjacent native-build environment restoration on the same facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
