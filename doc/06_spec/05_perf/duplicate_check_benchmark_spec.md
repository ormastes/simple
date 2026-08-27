# Duplicate Check Benchmark Specification

> Tests covering duplicate-check qualification benchmark.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Benchmark Specification

## Scenarios

### duplicate-check qualification benchmark

<details>
<summary>Advanced: measures repeated detection and reports real outcomes</summary>

#### measures repeated detection and reports real outcomes _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- measures repeated detection and reports real outcomes
   - Expected: rt_file_write_text(file_a, body) is true
   - Expected: rt_file_write_text(file_b, body) is true
   - Expected: stats.runs.len() equals `2`
   - Expected: stats.runs[0].files_count equals `2`
   - Expected: stats.runs[0].config_hash equals `stats.runs[1].config_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("measures repeated detection and reports real outcomes")
val root = "/tmp/simple_duplicate_benchmark"
val _ = rt_dir_create(root, true)
val body = "fn shared_logic(seed: i64) -> i64:\n    val base = seed + 1\n    val total = base * 2\n    return total\n"
val file_a = "{root}/a.spl"
val file_b = "{root}/b.spl"
expect(rt_file_write_text(file_a, body)).to_equal(true)
expect(rt_file_write_text(file_b, body)).to_equal(true)

val stats = run_benchmark_iterations("qualification", [file_a, file_b], benchmark_config(), 2)

expect(stats.runs.len()).to_equal(2)
expect(stats.runs[0].files_count).to_equal(2)
expect(stats.runs[0].groups_found).to_be_greater_than(0)
expect(stats.runs[0].config_hash).to_equal(stats.runs[1].config_hash)
expect(stats.min_ms).to_be_less_than(stats.max_ms + 1)
expect(format_benchmark_stats(stats)).to_contain("Benchmark Statistics (2 runs)")
```

</details>


</details>

<details>
<summary>Advanced: persists and reloads measured results</summary>

#### persists and reloads measured results _(slow)_

- persists and reloads measured results
   - Expected: rt_file_write_text(source, "fn measured():\n    val value = 1\n    return value\n") is true
   - Expected: loaded.len() equals `1`
   - Expected: loaded[0].name equals `persistence_iter_0`
   - Expected: loaded[0].files_count equals `1`
   - Expected: loaded[0].config_hash equals `stats.runs[0].config_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("persists and reloads measured results")
val root = "/tmp/simple_duplicate_benchmark_persistence"
val _ = rt_dir_create(root, true)
val source = "{root}/source.spl"
val output = "{root}/results.txt"
val _deleted = rt_file_delete(output)
expect(rt_file_write_text(source, "fn measured():\n    val value = 1\n    return value\n")).to_equal(true)
val stats = run_benchmark_iterations("persistence", [source], benchmark_config(), 1)

save_benchmark_results(stats.runs, output)
val loaded = load_benchmark_results(output)

expect(loaded.len()).to_equal(1)
expect(loaded[0].name).to_equal("persistence_iter_0")
expect(loaded[0].files_count).to_equal(1)
expect(loaded[0].config_hash).to_equal(stats.runs[0].config_hash)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/duplicate_check_benchmark_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering duplicate-check qualification benchmark.
- duplicate-check qualification benchmark

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ce7e8d3d406626b7ed60503dbb6ad3dd74ab817d441a6fe0d74954f64838e363`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce7e8d3d406626b7ed60503dbb6ad3dd74ab817d441a6fe0d74954f64838e363`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce7e8d3d406626b7ed60503dbb6ad3dd74ab817d441a6fe0d74954f64838e363`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/duplicate_check_benchmark_spec.spl
mirror: doc/06_spec/05_perf/duplicate_check_benchmark_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/duplicate_check_benchmark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/duplicate_check_benchmark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/duplicate_check_benchmark_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/duplicate_check_benchmark_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures repeated detection and reports real outcomes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/duplicate_check_benchmark_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists and reloads measured results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
