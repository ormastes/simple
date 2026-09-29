# Coverage Decisions Extraction — Last Link in the Branch-Coverage Chain

> section to `SIMPLE_COVERAGE_OUTPUT` containing a row with a real partial

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Decisions Extraction — Last Link in the Branch-Coverage Chain

section to `SIMPLE_COVERAGE_OUTPUT` containing a row with a real partial

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/test_runner_coverage_decisions_extraction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirements

- REQ-COV-DECISIONS-001: a single-spec `--coverage` run writes a `decisions`
  section to `SIMPLE_COVERAGE_OUTPUT` containing a row with a real partial
  denominator (`true_count > 0 and false_count == 0`, i.e. hit < total).
- REQ-COV-DECISIONS-002: a second spec's run against the same
  `SIMPLE_COVERAGE_OUTPUT` path merges its decision rows into the existing
  artifact (both rows present, keyed by id/file/line/column) rather than
  overwriting it.

## Plan

1. Write a minimal fixture spec with an `if`/`else` where only the `if` arm
   runs; run it through the seed binary with `SIMPLE_COVERAGE=1
   SIMPLE_COVERAGE_OUTPUT=<path> ... test <fixture> --coverage`.
2. Parse the written artifact with `parse_coverage_sdn` and assert a decision
   row has `true_count > 0` and `false_count == 0`.
3. Write a second, structurally-shifted fixture (different line/column so its
   decision id differs) and run it into the SAME output path.
4. Assert the artifact now contains rows from BOTH fixtures.

## Scenarios

### coverage decisions survive test-runner extraction and merge (last link, branch coverage chain)

#### writes a decisions section with a real partial-coverage row for a single spec

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes a decisions section with a real partial-coverage row for a single spec
   - Expected: wrote is true
   - Expected: code equals `0`
   - Expected: rt_file_exists(out_path) is true
   - Expected: cov.decisions.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes a decisions section with a real partial-coverage row for a single spec")
if not rt_file_exists(_seed_binary):
    pending("seed binary {_seed_binary} not built locally; skip rather than false-fail")
else:
    val tag = "{rt_getpid()}"
    val fixture = "/tmp/cov_decisions_fixture_a_{tag}.spl"
    val out_path = "/tmp/cov_decisions_out_a_{tag}.sdn"
    if rt_file_exists(out_path):
        val _ = rt_file_delete(out_path)
    val wrote = rt_file_write_text(fixture, _fixture_a(""))
    expect(wrote).to_equal(true)
    val cmd = "SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT={out_path} {_seed_binary} test {fixture} --coverage"
    val (_stdout, _stderr, code) = _run_shell(cmd)
    expect(code).to_equal(0)
    expect(rt_file_exists(out_path)).to_equal(true)
    val artifact = file_read(out_path)
    expect(artifact).to_contain("decisions |id, file, line, column, true_count, false_count|")
    val cov = parse_coverage_sdn(artifact)
    expect(cov.decisions.len() > 0).to_equal(true)
    var found_partial = false
    for r in cov.decisions:
        if r.true_count > 0 and r.false_count == 0:
            found_partial = true
    assert_true(found_partial)
    val _ = rt_file_delete(fixture)
    val _ = rt_file_delete(out_path)
```

</details>

#### merges a second spec's decisions into the same SIMPLE_COVERAGE_OUTPUT artifact instead of overwriting

- merges a second spec's decisions into the same SIMPLE_COVERAGE_OUTPUT artifact instead of overwriting
   - Expected: code1 equals `0`
   - Expected: code2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("merges a second spec's decisions into the same SIMPLE_COVERAGE_OUTPUT artifact instead of overwriting")
if not rt_file_exists(_seed_binary):
    pending("seed binary {_seed_binary} not built locally; skip rather than false-fail")
else:
    val tag = "{rt_getpid()}"
    val fixture1 = "/tmp/cov_decisions_fixture_b1_{tag}.spl"
    val fixture2 = "/tmp/cov_decisions_fixture_b2_{tag}.spl"
    val out_path = "/tmp/cov_decisions_out_b_{tag}.sdn"
    if rt_file_exists(out_path):
        val _ = rt_file_delete(out_path)
    # Pad fixture2's `if` onto a different source line/column than
    # fixture1's, so the two runs produce distinct decision ids/keys
    # instead of colliding on the same (id, file, line, column) —
    # a same-key collision would make "merged" indistinguishable from
    # "overwritten" (both show one row).
    val _ = rt_file_write_text(fixture1, _fixture_a(""))
    val _ = rt_file_write_text(fixture2, _fixture_a("\n\n\n"))
    val cmd1 = "SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT={out_path} {_seed_binary} test {fixture1} --coverage"
    val (_o1, _e1, code1) = _run_shell(cmd1)
    expect(code1).to_equal(0)
    val cmd2 = "SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT={out_path} {_seed_binary} test {fixture2} --coverage"
    val (_o2, _e2, code2) = _run_shell(cmd2)
    expect(code2).to_equal(0)
    val artifact = file_read(out_path)
    val cov = parse_coverage_sdn(artifact)
    # Both runs' rows must survive: at least 2 distinct decision keys.
    assert_true(cov.decisions.len() >= 2)
    val _ = rt_file_delete(fixture1)
    val _ = rt_file_delete(fixture2)
    val _ = rt_file_delete(out_path)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-COV-DECISIONS-001:`
- `REQ-COV-DECISIONS-002:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7b1bab619424878cb7c5db790f34bfd0a8ea7cba06730da3d879471d896bd2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7b1bab619424878cb7c5db790f34bfd0a8ea7cba06730da3d879471d896bd2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7b1bab619424878cb7c5db790f34bfd0a8ea7cba06730da3d879471d896bd2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/test_runner_coverage_decisions_extraction_spec.spl
mirror: doc/06_spec/03_system/check/test_runner_coverage_decisions_extraction_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/test_runner_coverage_decisions_extraction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/test_runner_coverage_decisions_extraction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/test_runner_coverage_decisions_extraction_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/test_runner_coverage_decisions_extraction_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes a decisions section with a real partial-coverage row for a single spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/test_runner_coverage_decisions_extraction_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges a second spec's decisions into the same SIMPLE_COVERAGE_OUTPUT artifact instead of overwriting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
