# GUI showcase performance probe-exit contract

> Prevents partial 4K/8K benchmark output from becoming retained performance evidence after the producer crashes or times out. The focused wrapper self-test does not launch a renderer and cannot prove the 200 FPS target.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI showcase performance probe-exit contract

Prevents partial 4K/8K benchmark output from becoming retained performance evidence after the producer crashes or times out. The focused wrapper self-test does not launch a renderer and cannot prove the 200 FPS target.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/gui_showcase_perf_probe_exit_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Prevents partial 4K/8K benchmark output from becoming retained performance
evidence after the producer crashes or times out. The focused wrapper self-test
does not launch a renderer and cannot prove the 200 FPS target.

## Scenarios

### GUI showcase performance probe exit

#### rejects every nonzero producer exit before parsing partial rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects every nonzero producer exit before parsing partial rows
- Run the zero, failure, and timeout exit classifier
   - Expected: code equals `0`
- Verify the producer gate uses the checked classifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects every nonzero producer exit before parsing partial rows")
step("Run the zero, failure, and timeout exit classifier")
val (stdout, _stderr, code) = process_run(
    "/bin/sh", ["scripts/check/check-widget-showcase-4k-200fps.shs", "--self-test"])
expect(code).to_equal(0)
expect(stdout).to_contain("widget_showcase_perf_probe_exit_self_test_status=pass")

step("Verify the producer gate uses the checked classifier")
val source = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")
expect(source).to_contain("if ! probe_exit_passes \"$probe_rc\"; then")
expect(source.contains("[ \"$probe_rc\" -ne 0 ] && ! grep")).to_be(false)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3585d4dd4be368317a22a0550ba6233f428011935fb8bde3b1c90d0431f703e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3585d4dd4be368317a22a0550ba6233f428011935fb8bde3b1c90d0431f703e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3585d4dd4be368317a22a0550ba6233f428011935fb8bde3b1c90d0431f703e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/gui_showcase_perf_probe_exit_contract_spec.spl
mirror: doc/06_spec/03_system/check/gui_showcase_perf_probe_exit_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/03_system/check/gui_showcase_perf_probe_exit_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_showcase_perf_probe_exit_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_showcase_perf_probe_exit_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/check/gui_showcase_perf_probe_exit_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gui_showcase_perf_probe_exit_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects every nonzero producer exit before parsing partial rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
