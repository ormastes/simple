# Claude Full array utils

> Pure Simple coverage for small array helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full array utils

Pure Simple coverage for small array helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/array_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for small array helpers.

## Scenarios

### Claude full array utils

#### intersperses separators between values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- intersperses separators between values
- Check separator placement
   - Expected: intersperse([], ",") equals `[]`
   - Expected: intersperse(["a"], ",") equals `["a"]`
   - Expected: intersperse(["a", "b", "c"], ",") equals `["a", ",", "b", ",", "c"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("intersperses separators between values")
step("Check separator placement")
expect(intersperse([], ",")).to_equal([])
expect(intersperse(["a"], ",")).to_equal(["a"])
expect(intersperse(["a", "b", "c"], ",")).to_equal(["a", ",", "b", ",", "c"])
expect(intersperseWithIndex(["a", "b", "c"], fn(index: i64) -> text:
    "#" + index.to_string()
)).to_equal(["a", "#1", "b", "#2", "c"])
```

</details>

#### counts truthy predicate results

- counts truthy predicate results
- Check bool count route
   - Expected: countTruthy([]) equals `0`
   - Expected: countTruthy([true, false, true]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts truthy predicate results")
step("Check bool count route")
expect(countTruthy([])).to_equal(0)
expect(countTruthy([true, false, true])).to_equal(2)
```

</details>

#### deduplicates while preserving first-seen order

- deduplicates while preserving first-seen order
- Check unique values
   - Expected: uniq([]) equals `[]`
   - Expected: uniq(["a", "b", "a", "c", "b"]) equals `["a", "b", "c"]`
   - Expected: containsText(["x", "y"], "z") is false
   - Expected: arrayUtilsParityScope() equals `text arrays, indexed separators, and bool counts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deduplicates while preserving first-seen order")
step("Check unique values")
expect(uniq([])).to_equal([])
expect(uniq(["a", "b", "a", "c", "b"])).to_equal(["a", "b", "c"])
expect(containsText(["x", "y"], "z")).to_equal(false)
expect(arrayUtilsParityScope()).to_equal("text arrays, indexed separators, and bool counts")
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8af97fa0475ac1a322ea129a34bb1d909c7715dc9538005ee18310051d6e5090`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8af97fa0475ac1a322ea129a34bb1d909c7715dc9538005ee18310051d6e5090`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8af97fa0475ac1a322ea129a34bb1d909c7715dc9538005ee18310051d6e5090`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/array_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/array_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/array_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/array_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/array_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/array_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'intersperses separators between values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/array_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts truthy predicate results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/array_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deduplicates while preserving first-seen order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
