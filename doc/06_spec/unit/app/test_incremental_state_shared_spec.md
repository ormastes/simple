# test_incremental_state_shared_spec

> Purpose: Prove that IncrementalTestState.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_incremental_state_shared_spec

Purpose: Prove that IncrementalTestState.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_incremental_state_shared_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that IncrementalTestState.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### IncrementalTestState

#### records and reloads runner cache entries without persisting a dep graph file

- records and reloads runner cache entries without persisting a dep graph file
- Verify: records and reloads runner cache entries without persisting a dep graph file
   - Expected: entry.result_status equals `0`
   - Expected: entry.result_passed equals `3`
   - Expected: entry.result_skipped equals `1`
   - Expected: file_exists(graph_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records and reloads runner cache entries without persisting a dep graph file")
step("Verify: records and reloads runner cache entries without persisting a dep graph file")
# @req: REQ-APP-INCREMENTALTESTSTATE-001
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
val cache_path = incremental_state_test_path("cache.sdn")
val graph_path = incremental_state_test_path("graph.sdn")
file_write(test_path, "use app.test_runner_new.test_runner_main.{discover_tests}\n")

val state = incremental_test_state_new(cache_path, "", false)
state.record_runner_result(test_path, 3, 0, 1, 42)
state.save()

val reloaded = incremental_test_state_load(cache_path, "", false)
val entry = reloaded.check_freshness(test_path)

expect(entry.result_status).to_equal(0)
expect(entry.result_passed).to_equal(3)
expect(entry.result_skipped).to_equal(1)
expect(file_exists(graph_path)).to_equal(false)
```

</details>

#### uses the shared dep graph in runner mode without reverse dependency tracking

- uses the shared dep graph in runner mode without reverse dependency tracking
- Verify: uses the shared dep graph in runner mode without reverse dependency tracking
   - Expected: entry.result_status equals `-1`
   - Expected: incremental_list_contains(deps, "src/app/test_dep_graph_shared.spl") is true
   - Expected: state.get_affected_tests("src/app/test_dep_graph_shared.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the shared dep graph in runner mode without reverse dependency tracking")
step("Verify: uses the shared dep graph in runner mode without reverse dependency tracking")
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
file_write(test_path, "use app.test_runner_new.test_runner_main.{discover_tests}\n")

val state = incremental_test_state_new(incremental_state_test_path("cache.sdn"), "", false)
val entry = state.check_freshness(test_path)
val deps = state.get_deps(test_path)

expect(entry.result_status).to_equal(-1)
expect(incremental_list_contains(deps, "src/app/test_dep_graph_shared.spl")).to_equal(true)
expect(state.get_affected_tests("src/app/test_dep_graph_shared.spl").len()).to_equal(0)
```

</details>

#### persists reverse dependencies in daemon mode

- persists reverse dependencies in daemon mode
- Verify: persists reverse dependencies in daemon mode
   - Expected: incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("persists reverse dependencies in daemon mode")
step("Verify: persists reverse dependencies in daemon mode")
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
file_write(test_path, "use app.test_daemon.daemon.{TestDaemon}\n")

val state = incremental_test_state_new(
    incremental_state_test_path("cache.sdn"),
    incremental_state_test_path("graph.sdn"),
    true
)
state.check_freshness(test_path)
state.save()

val reloaded = incremental_test_state_load(
    incremental_state_test_path("cache.sdn"),
    incremental_state_test_path("graph.sdn"),
    true
)

expect(incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path)).to_equal(true)
```

</details>

#### records and reloads daemon cache output with reverse dependency tracking

- records and reloads daemon cache output with reverse dependency tracking
- Verify: records and reloads daemon cache output with reverse dependency tracking
   - Expected: entry.result_status equals `2`
   - Expected: entry.result_output equals `line one\nline two`
   - Expected: incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records and reloads daemon cache output with reverse dependency tracking")
step("Verify: records and reloads daemon cache output with reverse dependency tracking")
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
val cache_path = incremental_state_test_path("cache.sdn")
val graph_path = incremental_state_test_path("graph.sdn")
file_write(test_path, "use app.test_daemon.daemon.{TestDaemon}\n")

val state = incremental_test_state_new(cache_path, graph_path, true)
state.record_daemon_result(test_path, 2, 1, 0, 0, 15, "line one\nline two")
state.save()

val reloaded = incremental_test_state_load(cache_path, graph_path, true)
val entry = reloaded.check_freshness(test_path)

expect(entry.result_status).to_equal(2)
expect(entry.result_output).to_equal("line one\nline two")
expect(incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-INCREMENTALTESTSTATE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58b453976230d934935831ac4d5e9a80ddfcf0dd1154345ebdc750e71c008236`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58b453976230d934935831ac4d5e9a80ddfcf0dd1154345ebdc750e71c008236`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58b453976230d934935831ac4d5e9a80ddfcf0dd1154345ebdc750e71c008236`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_incremental_state_shared_spec.spl
mirror: doc/06_spec/unit/app/test_incremental_state_shared_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_incremental_state_shared_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_incremental_state_shared_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_incremental_state_shared_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_incremental_state_shared_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records and reloads runner cache entries without persisting a dep graph file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_incremental_state_shared_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the shared dep graph in runner mode without reverse dependency tracking' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_incremental_state_shared_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists reverse dependencies in daemon mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
