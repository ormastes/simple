# Iteration3 Memleak Specification

> Tests covering Memleak iteration 3.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Iteration3 Memleak Specification

## Scenarios

### Memleak iteration 3

#### performs typical test workload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- performs typical test workload
   - Expected: data.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("performs typical test workload")
# Note: nested fn can't mutate outer closure vars, so we return the array
fn do_work() -> [text]:
    var out: [text] = []
    var k = 0
    while k < 10:
        out.push("iteration3_string_{k}_with_padding")
        k = k + 1
    out
val data = do_work()
expect(data.len()).to_equal(10)
```

</details>

#### reads final RSS for comparison

- reads final RSS for comparison
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads final RSS for comparison")
val status = rt_file_read_text("/proc/self/status") ?? ""
var rss_line = ""
if status != "":
    val lines = status.split("\n")
    for line in lines:
        if line.starts_with("VmRSS:"):
            rss_line = line
if rss_line != "":
    print "  [RSS] {rss_line}"
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/unit/memleak/iteration3_memleak_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Memleak iteration 3.
- Memleak iteration 3

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8bf590d61abf6b7fa9288069ba0323866327c734ae262a31d0c06e623a957237`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8bf590d61abf6b7fa9288069ba0323866327c734ae262a31d0c06e623a957237`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8bf590d61abf6b7fa9288069ba0323866327c734ae262a31d0c06e623a957237`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/memleak/iteration3_memleak_spec.spl
mirror: doc/06_spec/unit/memleak/iteration3_memleak_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/memleak/iteration3_memleak_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/memleak/iteration3_memleak_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/memleak/iteration3_memleak_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/memleak/iteration3_memleak_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'performs typical test workload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/iteration3_memleak_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads final RSS for comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
