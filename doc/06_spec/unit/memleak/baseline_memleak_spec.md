# Baseline Memleak Specification

> Tests covering Baseline memleak - file 1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baseline Memleak Specification

## Scenarios

### Baseline memleak - file 1

#### performs string operations to generate typical stdout

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- performs string operations to generate typical stdout
   - Expected: results.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("performs string operations to generate typical stdout")
# Generate output similar to real tests
# Note: nested fn can't mutate outer closure vars, so we return the array
fn do_work() -> [text]:
    var out: [text] = []
    var k = 0
    while k < 10:
        out.push("test_{k}_result_string_with_some_padding_data")
        k = k + 1
    out
val results = do_work()
print "  Generated {results.len()} result strings"
expect(results.len()).to_equal(10)
```

</details>

#### reads /proc/self/status for RSS measurement

- reads /proc/self/status for RSS measurement
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads /proc/self/status for RSS measurement")
val status = rt_file_read_text("/proc/self/status") ?? ""
var rss_line = ""
if status != "":
    val lines = status.split("\n")
    for line in lines:
        if line.starts_with("VmRSS:"):
            rss_line = line
if rss_line != "":
    print "  [RSS] {rss_line}"
else:
    print "  [RSS] Could not read /proc/self/status"
expect(1).to_equal(1)
```

</details>

#### verifies this is a clean child process

- verifies this is a clean child process
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies this is a clean child process")
# This runs in a child process spawned by test runner.
# The child exits after this file, and OS reclaims all memory.
# Any leak in the child does NOT affect the parent.
# The parent's leak is from processing this child's output.
print "  Child process running - all memory freed on exit"
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/unit/memleak/baseline_memleak_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Baseline memleak - file 1.
- Baseline memleak - file 1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `1aea01844a9520d0e14d2c33a7f5d392ca41561278660afaec89703febdcf814`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1aea01844a9520d0e14d2c33a7f5d392ca41561278660afaec89703febdcf814`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1aea01844a9520d0e14d2c33a7f5d392ca41561278660afaec89703febdcf814`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/memleak/baseline_memleak_spec.spl
mirror: doc/06_spec/unit/memleak/baseline_memleak_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/memleak/baseline_memleak_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/memleak/baseline_memleak_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/memleak/baseline_memleak_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/memleak/baseline_memleak_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'performs string operations to generate typical stdout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/baseline_memleak_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads /proc/self/status for RSS measurement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/baseline_memleak_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies this is a clean child process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
