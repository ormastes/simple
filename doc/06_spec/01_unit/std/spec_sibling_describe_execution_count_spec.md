# Similar-Problem Detection: Executed-Example Count Across Sibling Groups

> Generalizes the sibling-`describe`-drop defect class (hollow green: a spec file

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Similar-Problem Detection: Executed-Example Count Across Sibling Groups

Generalizes the sibling-`describe`-drop defect class (hollow green: a spec file

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/spec_sibling_describe_execution_count_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Generalizes the sibling-`describe`-drop defect class (hollow green: a spec file
that silently executes fewer examples than it declares, in ANY nesting shape,
while still reporting success).

Instead of trusting the runner's own tally, this spec makes the executed count
an in-file assertion: each example in the earlier sibling groups records itself
into a module-level accumulator, and the final example asserts the accumulator
observed every earlier group. If any group -- top-level sibling, nested
`describe`, or `context` -- is dropped, this example FAILS loudly rather than
leaving a quiet green.

Oracle also covers nesting: group D nests a child `describe` and a `context`
whose examples must also be counted.

## Scenarios

### detection group A

#### records A

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records A


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records A")
record("A")
assert_true(true)
```

</details>

### detection group B

#### records B

- records B


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records B")
record("B")
assert_true(true)
```

</details>

### detection group B child

#### records B-child

- records B-child


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records B-child")
record("B-child")
assert_true(true)
```

</details>

### detection group C

#### inside a context

#### records C-ctx

- records C-ctx


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records C-ctx")
record("C-ctx")
assert_true(true)
```

</details>

### detection group Z (verifier, declared last)

#### observed every earlier group's example, so nothing was dropped

- observed every earlier group's example, so nothing was dropped


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("observed every earlier group's example, so nothing was dropped")
# Any dropped group leaves its mark missing. Assert presence
# individually so the failure message names the dropped group.
assert_contains(executed_marks.join(","), "A")
assert_contains(executed_marks.join(","), "B")
assert_contains(executed_marks.join(","), "B-child")
assert_contains(executed_marks.join(","), "C-ctx")
assert_equal(executed_marks.len(), 4)
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4062e2fefee51ec104b04e6f0de343ceeecad4b11f1d8988f29370106b432f05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4062e2fefee51ec104b04e6f0de343ceeecad4b11f1d8988f29370106b432f05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4062e2fefee51ec104b04e6f0de343ceeecad4b11f1d8988f29370106b432f05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/spec_sibling_describe_execution_count_spec.spl
mirror: doc/06_spec/01_unit/std/spec_sibling_describe_execution_count_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/spec_sibling_describe_execution_count_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/spec_sibling_describe_execution_count_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/spec_sibling_describe_execution_count_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records A' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_sibling_describe_execution_count_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records B' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_sibling_describe_execution_count_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records B-child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
