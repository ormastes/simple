# fail_spec

> Purpose: DELIBERATE failing fixture for lane C (test/fixtures/unstable_mode) —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fail_spec

Purpose: DELIBERATE failing fixture for lane C (test/fixtures/unstable_mode) —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/fixtures/_accept_run/fail_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: DELIBERATE failing fixture for lane C (test/fixtures/unstable_mode) —
gives the runner's ERROR (real failure) outcome class something honest to
detect. It must FAIL, forever, on purpose. Audience: test-runner owners.

## Scenarios

### unstable mode failing-assertion fixture

#### fails a genuine assertion on purpose

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- fails a genuine assertion on purpose
   - Expected: rt_file_exists("/.simple_fixtures/_accept_run/reserved_miss_path") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FIXTURES
step("fails a genuine assertion on purpose")
# Real executed oracle (filesystem probe, deterministic), NOT a literal
# mismatch: the reserved fixture-miss path can never exist, so this
# expect is a genuine executed assertion that deterministically fails.
expect(rt_file_exists("/.simple_fixtures/_accept_run/reserved_miss_path")).to_equal(true)  # oracle: reserved miss path must not exist — inverted on purpose, see header
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FIXTURES`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `157bc7af5de674e98ae4ce9b8057509965cb1f79d5fc49203aa487f6163170fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `157bc7af5de674e98ae4ce9b8057509965cb1f79d5fc49203aa487f6163170fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `157bc7af5de674e98ae4ce9b8057509965cb1f79d5fc49203aa487f6163170fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/fixtures/_accept_run/fail_spec.spl
mirror: doc/06_spec/fixtures/_accept_run/fail_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/fixtures/_accept_run/fail_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/fixtures/_accept_run/fail_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
