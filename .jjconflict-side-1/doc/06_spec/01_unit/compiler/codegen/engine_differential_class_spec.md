# Engine Differential Class Specification

> Tests covering cross-engine differential gate defends the silent fail-open class, static fail-open audit gate covers both trees.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Differential Class Specification

## Scenarios

### cross-engine differential gate defends the silent fail-open class

#### proves it can FAIL before any run is trusted

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- proves it can FAIL before any run is trusted
- The gate's --selftest is fatal and runs before every real scan
- Fixture 1 replays the real access.rs:288 field collapse — a struct returned by value whose every field read returns field 0
- Fixture 3 replays a key ABSENT on one engine, the crash-after-partial-output shape an intersection-based comparator would silently pass
- Fixture 4 replays all engines truncating IDENTICALLY: the cells agree but no engine finished


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("proves it can FAIL before any run is trusted")
step("The gate's --selftest is fatal and runs before every real scan")
val out = run_gate("--selftest")

step("Fixture 1 replays the real access.rs:288 field collapse — a struct returned by value whose every field read returns field 0")
step("Fixture 3 replays a key ABSENT on one engine, the crash-after-partial-output shape an intersection-based comparator would silently pass")
step("Fixture 4 replays all engines truncating IDENTICALLY: the cells agree but no engine finished")
expect(last_line(out)).to_contain("PASS — 6 selftest fixture(s) checked, 0 failed")
```

</details>

#### reports a real observation count rather than a bare verdict

- reports a real observation count rather than a bare verdict
- A verdict that does not state how many cells were compared cannot be distinguished from one that compared none
- The house convention requires n > 0 in every PASS line — a `0 ... checked` verdict is ERROR, never a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a real observation count rather than a bare verdict")
step("A verdict that does not state how many cells were compared cannot be distinguished from one that compared none")
val out = run_gate("--selftest")

step("The house convention requires n > 0 in every PASS line — a `0 ... checked` verdict is ERROR, never a pass")
expect(out).to_contain("6 selftest fixture(s) checked")
expect(out.contains("0 selftest fixture(s) checked")).to_be_false()
```

</details>

#### names the disagreeing cells rather than only counting them

- names the disagreeing cells rather than only counting them
- A FAIL that says only 'engines differ' leaves the next reader to re-derive the finding by hand — which is how these defects survived
- Fixture 1 asserts the verdict names retval_w3_length and retval_w3_tag, the two fields that collapsed onto field 0; the selftest fails loudly if the comparator counts them without naming them


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the disagreeing cells rather than only counting them")
step("A FAIL that says only 'engines differ' leaves the next reader to re-derive the finding by hand — which is how these defects survived")
val out = run_gate("--selftest")

step("Fixture 1 asserts the verdict names retval_w3_length and retval_w3_tag, the two fields that collapsed onto field 0; the selftest fails loudly if the comparator counts them without naming them")
expect(last_line(out)).to_contain("PASS")
expect(out.contains("did not name the collapsed fields")).to_be_false()
```

</details>

### static fail-open audit gate covers both trees

#### proves it can FAIL before any scan is trusted

- proves it can FAIL before any scan is trusted
- The Rust seed and the pure-Simple compiler express the same defect differently, so the audit carries pattern families for both plus the shell lanes
- Fixture 1 replays access.rs:288 — an unwrap_or(0) on a field-index resolution — and must be reported as NEW and NAMED
- Fixture 3 replays a file that already had one baselined hit growing a second: presence-only baselining would pass it, making a known-bad file a place to hide new instances
- Fixture 6 replays the pre-push guards that laundered their own failure with '|| true' and exited 0 without checking anything
- Fixture 7 runs the detector regexes against REAL source, because a detector that matches nothing would make every scan vacuously clean


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("proves it can FAIL before any scan is trusted")
step("The Rust seed and the pure-Simple compiler express the same defect differently, so the audit carries pattern families for both plus the shell lanes")
val out = process_run("sh",
    ["-c", "sh scripts/check/check-no-new-fail-open.shs --selftest 2>&1"]).0

step("Fixture 1 replays access.rs:288 — an unwrap_or(0) on a field-index resolution — and must be reported as NEW and NAMED")
step("Fixture 3 replays a file that already had one baselined hit growing a second: presence-only baselining would pass it, making a known-bad file a place to hide new instances")
step("Fixture 6 replays the pre-push guards that laundered their own failure with '|| true' and exited 0 without checking anything")
step("Fixture 7 runs the detector regexes against REAL source, because a detector that matches nothing would make every scan vacuously clean")
expect(last_line(out)).to_contain("PASS — 7 selftest fixture(s) checked, 0 failed")
```

</details>

#### refuses to pass when it examined nothing

- refuses to pass when it examined nothing
- Pointing the audit at a directory that does not exist must ERROR, never PASS
- ERROR — nothing was checked, exit 2. A guard that passes having checked nothing is itself an instance of the class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("refuses to pass when it examined nothing")
step("Pointing the audit at a directory that does not exist must ERROR, never PASS")
val out = process_run("sh",
    ["-c", "sh scripts/check/check-no-new-fail-open.shs --root /nonexistent-fail-open-probe 2>&1"]).0

step("ERROR — nothing was checked, exit 2. A guard that passes having checked nothing is itself an instance of the class")
expect(last_line(out)).to_contain("ERROR — nothing was checked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/engine_differential_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cross-engine differential gate defends the silent fail-open class, static fail-open audit gate covers both trees.
- cross-engine differential gate defends the silent fail-open class
- static fail-open audit gate covers both trees

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22699fdb4415e5c3335083326e245fdfd47ea68e557268fa49728362c11b86cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22699fdb4415e5c3335083326e245fdfd47ea68e557268fa49728362c11b86cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22699fdb4415e5c3335083326e245fdfd47ea68e557268fa49728362c11b86cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/engine_differential_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/engine_differential_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/engine_differential_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/engine_differential_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/engine_differential_class_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves it can FAIL before any run is trusted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/engine_differential_class_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a real observation count rather than a bare verdict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/engine_differential_class_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the disagreeing cells rather than only counting them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
