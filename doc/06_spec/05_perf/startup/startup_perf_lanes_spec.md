# Startup Perf Lanes Specification

> Tests covering startup perf harness Phase D lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Perf Lanes Specification

## Scenarios

### startup perf harness Phase D lanes

#### measures all six lanes with p50 and p95 and writes an immutable manifest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- measures all six lanes with p50 and p95 and writes an immutable manifest
- Run the detector for real against the committed budgets
- SKIP (no binary) is acceptable and self-labeling; anything else must report every lane
- Verdict names all six lanes: version, help, warm, cold, smf-load, compile-body
- p95 is reported alongside p50 (plan: 'p50 AND p95'), never p50 alone
- Binary identity is in the verdict — timings without identity are worthless
- A manifest path line precedes the verdict, and the file exists with the plan's fields
   - Expected: mpath != "" is true
   - Expected: fcode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("measures all six lanes with p50 and p95 and writes an immutable manifest")
step("Run the detector for real against the committed budgets")
val (out, _code) = run_sh("sh " + CHECK + " 2>&1")
val v: text = verdict_of(out)

step("SKIP (no binary) is acceptable and self-labeling; anything else must report every lane")
if not v.starts_with("SKIP —"):
    step("Verdict names all six lanes: version, help, warm, cold, smf-load, compile-body")
    expect(v).to_contain("6 lane(s) measured")
    expect(v).to_contain("version p50=")
    expect(v).to_contain("help p50=")
    expect(v).to_contain("run-hello-warm p50=")
    expect(v).to_contain("run-hello-cold p50=")
    expect(v).to_contain("smf-load p50=")
    expect(v).to_contain("compile-body p50=")

    step("p95 is reported alongside p50 (plan: 'p50 AND p95'), never p50 alone")
    expect(v).to_contain("/p95=")

    step("Binary identity is in the verdict — timings without identity are worthless")
    expect(v).to_contain("binary=")

    step("A manifest path line precedes the verdict, and the file exists with the plan's fields")
    var mpath: text = ""
    for line in out.split("\n"):
        if line.starts_with("manifest: "):
            mpath = line.replace("manifest: ", "").trim()
    expect(mpath != "").to_equal(true)
    val (_o, fcode) = run_sh("test -f '" + mpath + "'")
    expect(fcode).to_equal(0)
    val m: text = read_file(mpath)
    expect(m).to_contain("binary_sha256:")
    expect(m).to_contain("host:")
    expect(m).to_contain("loadavg:")
    expect(m).to_contain("sample_count:")
    expect(m).to_contain("version_p50_ms:")
    expect(m).to_contain("version_p95_ms:")
    expect(m).to_contain("compile_hello_p50_ms:")
    expect(m).to_contain("run_hello_max_rss_kb:")
    expect(m).to_contain("run_hello_opens:")
    expect(m).to_contain("run_hello_mmaps:")
```

</details>

#### positive control: an absurd budget FAILs and a generous one PASSes, so the lane cannot pass vacuously

- positive control: an absurd budget FAILs and a generous one PASSes, so the lane cannot pass vacuously
- Run the fatal selftest — it feeds a 0ms budgets file (must FAIL) and a 99999999ms one (must PASS)
- The must-FAIL fixture actually fired a FAIL — a detector that cannot fail is not a detector
- The must-PASS fixture PASSed non-vacuously, with all 6 lanes measured
- A budgets file missing a lane key ERRORs — a lane can never be silently dropped
- All four fixtures held, so the selftest exits 0
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("positive control: an absurd budget FAILs and a generous one PASSes, so the lane cannot pass vacuously")
step("Run the fatal selftest — it feeds a 0ms budgets file (must FAIL) and a 99999999ms one (must PASS)")
val (out, code) = run_sh("sh " + CHECK + " --selftest 2>&1")

step("The must-FAIL fixture actually fired a FAIL — a detector that cannot fail is not a detector")
expect(out).to_contain("selftest fixture1 (must-FAIL 0ms budgets): FAIL as required")

step("The must-PASS fixture PASSed non-vacuously, with all 6 lanes measured")
expect(out).to_contain("selftest fixture2 (must-PASS absurd budgets): PASS with 6 lanes as required")

step("A budgets file missing a lane key ERRORs — a lane can never be silently dropped")
expect(out).to_contain("selftest fixture4 (must-ERROR missing lane key): ERROR as required")

step("All four fixtures held, so the selftest exits 0")
expect(out).to_contain("selftest OK: 4 fixture(s)")
expect(code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/startup/startup_perf_lanes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering startup perf harness Phase D lanes.
- startup perf harness Phase D lanes

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `83a5b921cab2c13fb367babd2ba61193cca40d18e775ce0dba4a74816346ce7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83a5b921cab2c13fb367babd2ba61193cca40d18e775ce0dba4a74816346ce7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83a5b921cab2c13fb367babd2ba61193cca40d18e775ce0dba4a74816346ce7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/05_perf/startup/startup_perf_lanes_spec.spl
mirror: doc/06_spec/05_perf/startup/startup_perf_lanes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/startup/startup_perf_lanes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/startup/startup_perf_lanes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/startup/startup_perf_lanes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/startup/startup_perf_lanes_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures all six lanes with p50 and p95 and writes an immutable manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/startup/startup_perf_lanes_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: an absurd budget FAILs and a generous one PASSes, so the lane cannot pass vacuously' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
