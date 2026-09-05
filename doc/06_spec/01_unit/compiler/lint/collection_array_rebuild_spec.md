# Collection Array Rebuild Specification

> Tests covering COLL007 array rebuild to pop last.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Array Rebuild Specification

## Scenarios

### COLL007 array rebuild to pop last

#### flags the colon open-ended slice form arr = arr[:-1]

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags the colon open-ended slice form arr = arr[:-1]
- Lint a loop that rebinds arr from an open-ended slice of itself
   - Expected: coll007_count("/tmp/coll007_open.spl", OPEN_SRC) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags the colon open-ended slice form arr = arr[:-1]")
step("Lint a loop that rebinds arr from an open-ended slice of itself")
expect(coll007_count("/tmp/coll007_open.spl", OPEN_SRC)).to_equal(1)
```

</details>

#### flags the colon explicit slice form arr = arr[0:arr.len()-1]

- flags the colon explicit slice form arr = arr[0:arr.len()-1]
- Lint a loop that rebinds arr from an explicit slice of itself
   - Expected: coll007_count("/tmp/coll007_full.spl", FULL_SRC) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags the colon explicit slice form arr = arr[0:arr.len()-1]")
step("Lint a loop that rebinds arr from an explicit slice of itself")
expect(coll007_count("/tmp/coll007_full.spl", FULL_SRC)).to_equal(1)
```

</details>

#### stays silent when the slice receiver is a different variable

- stays silent when the slice receiver is a different variable
- Lint a loop that assigns a slice of a DIFFERENT array into arr
   - Expected: coll007_count("/tmp/coll007_other.spl", OTHER_VAR_SRC) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays silent when the slice receiver is a different variable")
"""`arr = other[0:other.len()-1]` does not rebuild `arr` from
itself — flagging it would blame the wrong variable."""
step("Lint a loop that assigns a slice of a DIFFERENT array into arr")
expect(coll007_count("/tmp/coll007_other.spl", OTHER_VAR_SRC)).to_equal(0)
```

</details>

#### stays silent on the already-fixed .pop() form

- stays silent on the already-fixed .pop() form
- Lint a loop that already uses .pop() instead of rebuilding
   - Expected: coll007_count("/tmp/coll007_fixed.spl", ALREADY_FIXED_SRC) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays silent on the already-fixed .pop() form")
step("Lint a loop that already uses .pop() instead of rebuilding")
expect(coll007_count("/tmp/coll007_fixed.spl", ALREADY_FIXED_SRC)).to_equal(0)
```

</details>

#### stays silent on the invalid arr[0..arr.len()-1] range-index form

- stays silent on the invalid arr[0..arr.len()-1] range-index form
- Lint a loop written with the non-slicing `..` range operator
   - Expected: coll007_count("/tmp/coll007_dotdot.spl", DOTDOT_SRC) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays silent on the invalid arr[0..arr.len()-1] range-index form")
"""`..` builds a Range value, not a slice; indexing an array by a
Range errors at runtime. This is not runnable code, so the rule
must not warn on it — matching it would train people to write
code that cannot execute."""
step("Lint a loop written with the non-slicing `..` range operator")
expect(coll007_count("/tmp/coll007_dotdot.spl", DOTDOT_SRC)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/collection_array_rebuild_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering COLL007 array rebuild to pop last.
- COLL007 array rebuild to pop last

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

- Canonical SPipe generation for source `589331cdb435abcb16bd5fe668999ca243b9ffef637a62fdef13d9be70da2f8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `589331cdb435abcb16bd5fe668999ca243b9ffef637a62fdef13d9be70da2f8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `589331cdb435abcb16bd5fe668999ca243b9ffef637a62fdef13d9be70da2f8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/collection_array_rebuild_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/collection_array_rebuild_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/collection_array_rebuild_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/collection_array_rebuild_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/collection_array_rebuild_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/collection_array_rebuild_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags the colon open-ended slice form arr = arr[:-1]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/collection_array_rebuild_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags the colon explicit slice form arr = arr[0:arr.len()-1]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/collection_array_rebuild_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays silent when the slice receiver is a different variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
