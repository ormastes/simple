# Claude Full EffortCallout Component

> Checks effort level normalization, warning state, actions, estimates, and collapse rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full EffortCallout Component

Checks effort level normalization, warning state, actions, estimates, and collapse rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/effort_callout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks effort level normalization, warning state, actions, estimates, and collapse rendering.

## Scenarios

### Claude full EffortCallout component

#### normalizes effort levels and estimates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes effort levels and estimates
- Map aliases and clamp estimates
   - Expected: normalizeEffortLevel("minimal") equals `low`
   - Expected: normalizeEffortLevel("normal") equals `medium`
   - Expected: normalizeEffortLevel("deep") equals `high`
   - Expected: normalizeEffortLevel("ultrathink") equals `maximum`
   - Expected: effortLevelLabel("maximum") equals `Maximum effort`
   - Expected: estimate.inputTokens equals `0`
   - Expected: estimate.totalTokens() equals `1200`
   - Expected: formatEffortCost(7) equals `$0.07`
   - Expected: formatEffortDuration(125) equals `2m 5s`
   - Expected: defaultEffortEstimate("high").costCents equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes effort levels and estimates")
step("Map aliases and clamp estimates")
expect(normalizeEffortLevel("minimal")).to_equal("low")
expect(normalizeEffortLevel("normal")).to_equal("medium")
expect(normalizeEffortLevel("deep")).to_equal("high")
expect(normalizeEffortLevel("ultrathink")).to_equal("maximum")
expect(effortLevelLabel("maximum")).to_equal("Maximum effort")

val estimate = EffortEstimate.new(-1, 1200, 7, 125)
expect(estimate.inputTokens).to_equal(0)
expect(estimate.totalTokens()).to_equal(1200)
expect(formatEffortCost(7)).to_equal("$0.07")
expect(formatEffortDuration(125)).to_equal("2m 5s")
expect(defaultEffortEstimate("high").costCents).to_equal(120)
```

</details>

#### renders collapsed and expanded warning states

- renders collapsed and expanded warning states
- Render warning body and selected action
   - Expected: state.noticeKind equals `warning`
   - Expected: state.title equals `High effort`
   - Expected: recommendedEffortActionLabel(state) equals `Use medium`
   - Expected: effortToggleLabel(state) equals `Hide details`
   - Expected: collapsed.collapsed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders collapsed and expanded warning states")
step("Render warning body and selected action")
val state = EffortCalloutState.new("high", "", "", "", false, defaultEffortEstimate("high"), defaultEffortActions("high"), "lower")
expect(state.noticeKind).to_equal("warning")
expect(state.title).to_equal("High effort")
expect(recommendedEffortActionLabel(state)).to_equal("Use medium")
expect(effortSummaryLine(state)).to_contain("54.0k")
expect(effortEstimateLine(state.estimate)).to_contain("$1.20")
expect(effortToggleLabel(state)).to_equal("Hide details")

val rendered = renderEffortCallout(state)
expect(rendered).to_contain("Higher usage expected [yellow] High effort")
expect(rendered).to_contain("Recommended: Use medium")
expect(rendered).to_contain("* Use medium [primary]")

val collapsed = state.collapse()
expect(collapsed.collapsed).to_equal(true)
expect(renderEffortCallout(collapsed)).to_contain("Show details")
```

</details>

#### tracks action selection and parity helpers

- tracks action selection and parity helpers
- Select actions and expose parity metadata
   - Expected: action.tone() equals `warning`
   - Expected: state.activeActionId equals `cancel`
   - Expected: recommendedEffortActionLabel(state) equals `Cancel`
   - Expected: effortCalloutModeledActionCount("maximum") equals `3`
   - Expected: effortCalloutModeledStateCount() equals `3`
   - Expected: effortCalloutModeledSourceFile() equals `src/components/EffortCallout.tsx`
   - Expected: effortCalloutSourceLinesModeled() equals `264`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks action selection and parity helpers")
step("Select actions and expose parity metadata")
val action = EffortAction.new("cancel", "Cancel", "Stop request", false, true)
expect(action.tone()).to_equal("warning")

val state = EffortCalloutState.compact("maximum").expand().selectAction("cancel")
expect(state.activeActionId).to_equal("cancel")
expect(recommendedEffortActionLabel(state)).to_equal("Cancel")
expect(effortCalloutModeledActionCount("maximum")).to_equal(3)
expect(effortCalloutModeledStateCount()).to_equal(3)
expect(effortCalloutModeledSourceFile()).to_equal("src/components/EffortCallout.tsx")
expect(effortCalloutSourceLinesModeled()).to_equal(264)
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

- Canonical SPipe generation for source `87b0e74908ce6d7fb499daf96be1d75351a9c3b66a42acf4ca7627fe5ba66196`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87b0e74908ce6d7fb499daf96be1d75351a9c3b66a42acf4ca7627fe5ba66196`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87b0e74908ce6d7fb499daf96be1d75351a9c3b66a42acf4ca7627fe5ba66196`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/effort_callout_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/effort_callout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/effort_callout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/effort_callout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/effort_callout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/effort_callout_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes effort levels and estimates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/effort_callout_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders collapsed and expanded warning states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/effort_callout_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks action selection and parity helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
