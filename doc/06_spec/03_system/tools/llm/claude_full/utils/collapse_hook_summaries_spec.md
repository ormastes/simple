# Claude Full collapse hook summaries

> Pure Simple coverage for consecutive hook summary collapsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full collapse hook summaries

Pure Simple coverage for consecutive hook summary collapsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for consecutive hook summary collapsing.

## Scenarios

### Claude full collapse hook summaries

#### collapses consecutive labeled summaries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collapses consecutive labeled summaries
- Check aggregate fields
   - Expected: out.len() equals `1`
   - Expected: out[0].hookCount equals `5`
   - Expected: out[0].hookInfos equals `["a", "b"]`
   - Expected: out[0].hookErrors equals `["e1", "e2"]`
   - Expected: out[0].preventedContinuation is true
   - Expected: out[0].hasOutput is true
   - Expected: out[0].totalDurationMs equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses consecutive labeled summaries")
step("Check aggregate fields")
val messages = [
    hookSummaryMessage("system", "stop_hook_summary", "PostToolUse", 2, ["a"], ["e1"], false, true, 10),
    hookSummaryMessage("system", "stop_hook_summary", "PostToolUse", 3, ["b"], ["e2"], true, false, 25),
]
val out = collapseHookSummaries(messages)
expect(out.len()).to_equal(1)
expect(out[0].hookCount).to_equal(5)
expect(out[0].hookInfos).to_equal(["a", "b"])
expect(out[0].hookErrors).to_equal(["e1", "e2"])
expect(out[0].preventedContinuation).to_equal(true)
expect(out[0].hasOutput).to_equal(true)
expect(out[0].totalDurationMs).to_equal(25)
```

</details>

#### keeps a single labeled summary unchanged

- keeps a single labeled summary unchanged
- Check single item path
   - Expected: out.len() equals `1`
   - Expected: out[0].hookCount equals `1`
   - Expected: out[0].hookInfos equals `["a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps a single labeled summary unchanged")
step("Check single item path")
val out = collapseHookSummaries([hookSummaryMessage("system", "stop_hook_summary", "PreToolUse", 1, ["a"], [], false, false, 7)])
expect(out.len()).to_equal(1)
expect(out[0].hookCount).to_equal(1)
expect(out[0].hookInfos).to_equal(["a"])
```

</details>

#### only collapses consecutive matching labels

- only collapses consecutive matching labels
- Check label boundary
   - Expected: out.len() equals `3`
   - Expected: out[0].hookInfos equals `["a1"]`
   - Expected: out[2].hookInfos equals `["a2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("only collapses consecutive matching labels")
step("Check label boundary")
val out = collapseHookSummaries([
    hookSummaryMessage("system", "stop_hook_summary", "A", 1, ["a1"], [], false, false, 1),
    hookSummaryMessage("system", "stop_hook_summary", "B", 1, ["b"], [], false, false, 2),
    hookSummaryMessage("system", "stop_hook_summary", "A", 1, ["a2"], [], false, false, 3),
])
expect(out.len()).to_equal(3)
expect(out[0].hookInfos).to_equal(["a1"])
expect(out[2].hookInfos).to_equal(["a2"])
```

</details>

#### preserves unlabeled and non-hook messages

- preserves unlabeled and non-hook messages
- Check non-summary path
   - Expected: out.len() equals `2`
   - Expected: isLabeledHookSummary(out[0]) is false
   - Expected: out[1].typeName equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves unlabeled and non-hook messages")
step("Check non-summary path")
val out = collapseHookSummaries([
    hookSummaryMessage("system", "stop_hook_summary", "", 1, ["empty"], [], false, false, 1),
    hookSummaryMessage("assistant", "stop_hook_summary", "A", 1, ["assistant"], [], false, false, 2),
])
expect(out.len()).to_equal(2)
expect(isLabeledHookSummary(out[0])).to_equal(false)
expect(out[1].typeName).to_equal("assistant")
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

- Canonical SPipe generation for source `5a9542a93f67e92424f0c9fd0e4c7c4c887039e4e644eda309af1cc4e0ceaf6e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a9542a93f67e92424f0c9fd0e4c7c4c887039e4e644eda309af1cc4e0ceaf6e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a9542a93f67e92424f0c9fd0e4c7c4c887039e4e644eda309af1cc4e0ceaf6e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses consecutive labeled summaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a single labeled summary unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/collapse_hook_summaries_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'only collapses consecutive matching labels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
