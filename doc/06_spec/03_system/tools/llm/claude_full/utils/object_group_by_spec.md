# Claude Full object group by

> Pure Simple coverage for objectGroupBy-style text grouping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full object group by

Pure Simple coverage for objectGroupBy-style text grouping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/object_group_by_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for objectGroupBy-style text grouping.

## Scenarios

### Claude full object group by

#### groups text values by first-seen keys

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- groups text values by first-seen keys
- Check grouped values
   - Expected: groups.len() equals `2`
   - Expected: groups[0].key equals `a`
   - Expected: groups[0].values equals `["a1", "a2"]`
   - Expected: groups[1].key equals `b`
   - Expected: groups[1].values equals `["b1"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("groups text values by first-seen keys")
step("Check grouped values")
val groups = objectGroupByText(["a1", "b1", "a2"], ["a", "b", "a"])
expect(groups.len()).to_equal(2)
expect(groups[0].key).to_equal("a")
expect(groups[0].values).to_equal(["a1", "a2"])
expect(groups[1].key).to_equal("b")
expect(groups[1].values).to_equal(["b1"])
```

</details>

#### preserves empty input

- preserves empty input
- Check empty grouping
   - Expected: objectGroupByText([], []).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves empty input")
step("Check empty grouping")
expect(objectGroupByText([], []).len()).to_equal(0)
```

</details>

#### uses only keyed items

- uses only keyed items
- Check short key list
   - Expected: groups.len() equals `1`
   - Expected: groups[0].values equals `["first"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses only keyed items")
step("Check short key list")
val groups = objectGroupByText(["first", "ignored"], ["k"])
expect(groups.len()).to_equal(1)
expect(groups[0].values).to_equal(["first"])
```

</details>

#### documents the parity scope

- documents the parity scope
- Check scope marker
   - Expected: objectGroupByParityScope() equals `text values grouped by selected key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents the parity scope")
step("Check scope marker")
expect(objectGroupByParityScope()).to_equal("text values grouped by selected key")
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

- Canonical SPipe generation for source `2243adfb631919515cb41d5344d26f1aa8ad4c700ad3a3b3b2b7fd1a817210cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2243adfb631919515cb41d5344d26f1aa8ad4c700ad3a3b3b2b7fd1a817210cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2243adfb631919515cb41d5344d26f1aa8ad4c700ad3a3b3b2b7fd1a817210cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/object_group_by_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/object_group_by_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/object_group_by_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/object_group_by_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/object_group_by_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/object_group_by_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups text values by first-seen keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/object_group_by_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/object_group_by_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses only keyed items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
