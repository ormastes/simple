# @manual: primary

> Purpose: Prove that Async Effects.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Async Effects.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/03_system/feature/usage/async_effects_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Async Effects.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-ASYNC-EFFECTS-001
doc/01_research/feature/REQ-FEATURE-ASYNC-EFFECTS-001.md
doc/03_plan/feature/REQ-FEATURE-ASYNC-EFFECTS-001.md
doc/04_architecture/feature/REQ-FEATURE-ASYNC-EFFECTS-001.md
doc/05_design/feature/REQ-FEATURE-ASYNC-EFFECTS-001.md

## Scenarios

### Async Effects

#### suspends an effectful computation until the scheduler resumes it

- Spawn a task and confirm it has not run before resume


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-ASYNC-EFFECTS-001
step("Spawn a task and confirm it has not run before resume")
AE_LOG = ""
val handle = green_spawn(ae_stage_one)
assert_equal(AE_LOG, "")
assert_equal(green_run_one(), true)
assert_equal(AE_LOG, "one;")
assert_equal(handle.join(), 1)
```

</details>

#### propagates an effect failure through the scheduler to the caller

- Run a failing effectful task and read back its error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-ASYNC-EFFECTS-001
step("Run a failing effectful task and read back its error")
AE_LOG = ""
val handle = green_spawn(ae_stage_failing)
assert_equal(green_run_one(), true)
assert_equal(AE_LOG, "fail;")
assert_equal(green_task_error(handle.id()), "async-effects probe failure")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b71dceba6acd65f0e68ccc2a62565642ee25a36ca06a22e397a9b607b32e1d38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b71dceba6acd65f0e68ccc2a62565642ee25a36ca06a22e397a9b607b32e1d38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b71dceba6acd65f0e68ccc2a62565642ee25a36ca06a22e397a9b607b32e1d38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/usage/async_effects_spec.spl
mirror: doc/06_spec/03_system/feature/usage/async_effects_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=65 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/async_effects_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/usage/async_effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/async_effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/async_effects_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'suspends an effectful computation until the scheduler resumes it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/async_effects_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates an effect failure through the scheduler to the caller' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
