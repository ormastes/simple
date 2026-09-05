# Claude Full set utils

> Pure Simple coverage for text-array set operation parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full set utils

Pure Simple coverage for text-array set operation parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/set_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for text-array set operation parity.

## Scenarios

### Claude full set utils

#### computes difference while preserving left-side order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes difference while preserving left-side order
- Check difference
   - Expected: difference(["a", "b", "c"], ["b"]) equals `["a", "c"]`
   - Expected: difference(["a", "a", "b"], ["b"]) equals `["a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes difference while preserving left-side order")
step("Check difference")
expect(difference(["a", "b", "c"], ["b"])).to_equal(["a", "c"])
expect(difference(["a", "a", "b"], ["b"])).to_equal(["a"])
```

</details>

#### detects intersections

- detects intersections
- Check intersection
   - Expected: intersects([], ["a"]) is false
   - Expected: intersects(["a", "b"], ["c"]) is false
   - Expected: intersects(["a", "b"], ["b", "c"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects intersections")
step("Check intersection")
expect(intersects([], ["a"])).to_equal(false)
expect(intersects(["a", "b"], ["c"])).to_equal(false)
expect(intersects(["a", "b"], ["b", "c"])).to_equal(true)
```

</details>

#### checks whether every left value exists in the right set

- checks whether every left value exists in the right set
- Check every
   - Expected: every([], ["a"]) is true
   - Expected: every(["a", "b"], ["b", "a", "c"]) is true
   - Expected: every(["a", "d"], ["a", "b"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks whether every left value exists in the right set")
step("Check every")
expect(every([], ["a"])).to_equal(true)
expect(every(["a", "b"], ["b", "a", "c"])).to_equal(true)
expect(every(["a", "d"], ["a", "b"])).to_equal(false)
```

</details>

#### unions values while preserving first-seen order

- unions values while preserving first-seen order
- Check union
   - Expected: union(["a", "b"], ["b", "c"]) equals `["a", "b", "c"]`
   - Expected: union([], ["x"]) equals `["x"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unions values while preserving first-seen order")
step("Check union")
expect(union(["a", "b"], ["b", "c"])).to_equal(["a", "b", "c"])
expect(union([], ["x"])).to_equal(["x"])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `da828932e8937fc53d3d089cf8abf788b1f274dac241ffb09cfde7ee5f676b56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da828932e8937fc53d3d089cf8abf788b1f274dac241ffb09cfde7ee5f676b56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da828932e8937fc53d3d089cf8abf788b1f274dac241ffb09cfde7ee5f676b56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/set_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/set_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/set_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes difference while preserving left-side order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/set_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects intersections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/set_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks whether every left value exists in the right set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
