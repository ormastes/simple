# Claude Full content array utils

> Pure Simple coverage for content block placement around tool results.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full content array utils

Pure Simple coverage for content block placement around tool results.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/content_array_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for content block placement around tool results.

## Scenarios

### Claude full content array utils

#### inserts after the last tool result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- inserts after the last tool result
- Check tool result placement
   - Expected: out.len() equals `5`
   - Expected: out[3].typeName equals `cache_control`
   - Expected: out[4].text equals `end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inserts after the last tool result")
step("Check tool result placement")
val out = insertBlockAfterToolResults([contentBlock("tool_result", "one"), contentBlock("text", "tail"), contentBlock("tool_result", "two"), contentBlock("text", "end")], contentBlock("cache_control", "x"))
expect(out.len()).to_equal(5)
expect(out[3].typeName).to_equal("cache_control")
expect(out[4].text).to_equal("end")
```

</details>

#### appends a text continuation when inserted after final tool result

- appends a text continuation when inserted after final tool result
- Check continuation
   - Expected: out.len() equals `4`
   - Expected: out[2].typeName equals `cache_control`
   - Expected: out[3].typeName equals `text`
   - Expected: out[3].text equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("appends a text continuation when inserted after final tool result")
step("Check continuation")
val out = insertBlockAfterToolResults([contentBlock("text", "lead"), contentBlock("tool_result", "two")], contentBlock("cache_control", "x"))
expect(out.len()).to_equal(4)
expect(out[2].typeName).to_equal("cache_control")
expect(out[3].typeName).to_equal("text")
expect(out[3].text).to_equal(".")
```

</details>

#### inserts before the last block without tool results

- inserts before the last block without tool results
- Check fallback placement
   - Expected: out.len() equals `3`
   - Expected: out[1].typeName equals `cache_control`
   - Expected: out[2].text equals `last`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inserts before the last block without tool results")
step("Check fallback placement")
val out = insertBlockAfterToolResults([contentBlock("text", "first"), contentBlock("text", "last")], contentBlock("cache_control", "x"))
expect(out.len()).to_equal(3)
expect(out[1].typeName).to_equal("cache_control")
expect(out[2].text).to_equal("last")
```

</details>

#### handles empty content

- handles empty content
- Check empty placement
   - Expected: out.len() equals `1`
   - Expected: out[0].typeName equals `cache_control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty content")
step("Check empty placement")
val out = insertBlockAfterToolResults([], contentBlock("cache_control", "x"))
expect(out.len()).to_equal(1)
expect(out[0].typeName).to_equal("cache_control")
```

</details>

#### finds the last tool result index

- finds the last tool result index
- Check index helper
   - Expected: findLastToolResultIndex([contentBlock("tool_result", "a"), contentBlock("text", "b"), contentBlock("tool_result", "c")]) equals `2`
   - Expected: findLastToolResultIndex([contentBlock("text", "a")]) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds the last tool result index")
step("Check index helper")
expect(findLastToolResultIndex([contentBlock("tool_result", "a"), contentBlock("text", "b"), contentBlock("tool_result", "c")])).to_equal(2)
expect(findLastToolResultIndex([contentBlock("text", "a")])).to_equal(-1)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `40401a06056a9216c4f0c324f1762a9d3e12cc2874ae5bbf7baf82a63f840d70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40401a06056a9216c4f0c324f1762a9d3e12cc2874ae5bbf7baf82a63f840d70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40401a06056a9216c4f0c324f1762a9d3e12cc2874ae5bbf7baf82a63f840d70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/content_array_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/content_array_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/content_array_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/content_array_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/content_array_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/content_array_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts after the last tool result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/content_array_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends a text continuation when inserted after final tool result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/content_array_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts before the last block without tool results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
