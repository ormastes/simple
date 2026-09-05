# Termination Census Scan Specification

> Tests covering termination census scan — loop bounds, termination census scan — recursion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Termination Census Scan Specification

## Scenarios

### termination census scan — loop bounds

<details>
<summary>Advanced: classifies an integer-literal range for-loop as bounded</summary>

#### classifies an integer-literal range for-loop as bounded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies an integer-literal range for-loop as bounded
   - Expected: v.verdict equals `bounded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies an integer-literal range for-loop as bounded")
val verdicts = scan_single_file_loops("fixture/range.spl", range_bounded_source())
val v = find_verdict(verdicts, "sum_first_ten")
expect(v.verdict).to_equal("bounded")
```

</details>


</details>

#### classifies a fixed-capacity collection iteration as bounded

- classifies a fixed-capacity collection iteration as bounded
   - Expected: v.verdict equals `bounded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies a fixed-capacity collection iteration as bounded")
val verdicts = scan_single_file_loops("fixture/fixed.spl", fixed_collection_source())
val v = find_verdict(verdicts, "sum_slots")
expect(v.verdict).to_equal("bounded")
```

</details>

<details>
<summary>Advanced: classifies an unbounded while-loop as unknown and names the function</summary>

#### classifies an unbounded while-loop as unknown and names the function

- classifies an unbounded while-loop as unknown and names the function
   - Expected: v.verdict equals `unknown`
   - Expected: v.fn_name equals `poll_forever`
   - Expected: v.path equals `fixture/while.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies an unbounded while-loop as unknown and names the function")
val verdicts = scan_single_file_loops("fixture/while.spl", unbounded_while_source())
val v = find_verdict(verdicts, "poll_forever")
expect(v.verdict).to_equal("unknown")
expect(v.fn_name).to_equal("poll_forever")
expect(v.path).to_equal("fixture/while.spl")
expect(v.detail).to_contain("while-loop")
```

</details>


</details>

<details>
<summary>Advanced: classifies a for-loop over an unrecognized iterable as unknown, not bounded</summary>

#### classifies a for-loop over an unrecognized iterable as unknown, not bounded

- classifies a for-loop over an unrecognized iterable as unknown, not bounded
   - Expected: v.verdict equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies a for-loop over an unrecognized iterable as unknown, not bounded")
val verdicts = scan_single_file_loops("fixture/list.spl", unrecognized_for_source())
val v = find_verdict(verdicts, "sum_list")
expect(v.verdict).to_equal("unknown")
```

</details>


</details>

### termination census scan — recursion

#### flags two mutually-recursive functions as one SCC

- flags two mutually-recursive functions as one SCC
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags two mutually-recursive functions as one SCC")
val sccs = scan_sources_recursion(mutual_recursion_sources())
var found = false
for s in sccs:
    if s.members.len() == 2:
        val has_even = s.members[0] == "is_even" or s.members[1] == "is_even"
        val has_odd = s.members[0] == "is_odd" or s.members[1] == "is_odd"
        if has_even and has_odd:
            found = true
expect(found).to_equal(true)
```

</details>

<details>
<summary>Advanced: flags a self-recursive function as its own self-loop SCC</summary>

#### flags a self-recursive function as its own self-loop SCC

- flags a self-recursive function as its own self-loop SCC
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags a self-recursive function as its own self-loop SCC")
var m: Dict<text, text> = {}
m["fixture/self.spl"] = self_recursion_source()
val sccs = scan_sources_recursion(m)
var found = false
for s in sccs:
    if s.self_loop and s.members.len() == 1 and s.members[0] == "countdown":
        found = true
expect(found).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/termination_census_scan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering termination census scan — loop bounds, termination census scan — recursion.
- termination census scan — loop bounds
- termination census scan — recursion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `39c6decf72a32ab26bb84d5c74f631f93a91748de9c95f9972bfa60e0a09343c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `39c6decf72a32ab26bb84d5c74f631f93a91748de9c95f9972bfa60e0a09343c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `39c6decf72a32ab26bb84d5c74f631f93a91748de9c95f9972bfa60e0a09343c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/quality/code_quality/termination_census_scan_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/termination_census_scan_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/termination_census_scan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/termination_census_scan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/termination_census_scan_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies an integer-literal range for-loop as bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/termination_census_scan_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies a fixed-capacity collection iteration as bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/termination_census_scan_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies an unbounded while-loop as unknown and names the function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
