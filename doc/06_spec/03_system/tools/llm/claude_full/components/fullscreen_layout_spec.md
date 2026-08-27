# Claude Full FullscreenLayout

> Checks fullscreen panels, overlays, focus movement, responsive dimensions, and action summaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full FullscreenLayout

Checks fullscreen panels, overlays, focus movement, responsive dimensions, and action summaries.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks fullscreen panels, overlays, focus movement, responsive dimensions, and action summaries.

## Scenarios

### Claude full FullscreenLayout

#### models wide layout dimensions and focus

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models wide layout dimensions and focus
- Create three visible weighted panels
   - Expected: fullscreenLayoutMode(state.dimensions, state.compactRequested) equals `wide`
   - Expected: fullscreenHeaderVisible(state) is true
   - Expected: fullscreenFooterVisible(state) is true
   - Expected: fullscreenContentHeight(state) equals `34`
   - Expected: fullscreenFocusRegion(state) equals `composer`
   - Expected: fullscreenMoveFocus(state, "next") equals `tools`
   - Expected: fullscreenMoveFocus(state, "previous") equals `transcript`
   - Expected: frames.len() equals `3`
   - Expected: frames[0].x equals `0`
   - Expected: frames[0].height equals `34`
   - Expected: frames[1].focused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models wide layout dimensions and focus")
step("Create three visible weighted panels")
val panels = [
    FullscreenPanel.new("transcript", "Transcript", "main", 20, 5, 3, true, true),
    FullscreenPanel.new("composer", "Composer", "input", 20, 5, 1, true, false),
    FullscreenPanel.new("tools", "Tools", "sidebar", 10, 5, 1, true, true),
]
val state = FullscreenLayoutState.new(FullscreenDimensions.new(120, 40), panels, [], "composer", true, true, false, false, "Ready")

expect(fullscreenLayoutMode(state.dimensions, state.compactRequested)).to_equal("wide")
expect(fullscreenHeaderVisible(state)).to_equal(true)
expect(fullscreenFooterVisible(state)).to_equal(true)
expect(fullscreenContentHeight(state)).to_equal(34)
expect(fullscreenFocusRegion(state)).to_equal("composer")
expect(fullscreenMoveFocus(state, "next")).to_equal("tools")
expect(fullscreenMoveFocus(state, "previous")).to_equal("transcript")

val frames = fullscreenRegionFrames(state)
expect(frames.len()).to_equal(3)
expect(frames[0].x).to_equal(0)
expect(frames[0].height).to_equal(34)
expect(frames[1].focused).to_equal(true)
expect(frames[2].width).to_be_greater_than(0)
```

</details>

#### uses stacked and short responsive modes

- uses stacked and short responsive modes
- Narrow terminals stack panels
   - Expected: fullscreenLayoutMode(narrow.dimensions, false) equals `stacked`
- Short terminals keep only the focused frame
   - Expected: fullscreenLayoutMode(short.dimensions, false) equals `short`
   - Expected: fullscreenRegionFrames(short).len() equals `1`
   - Expected: fullscreenRegionFrames(short)[0].id equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses stacked and short responsive modes")
step("Narrow terminals stack panels")
val panels = [
    FullscreenPanel.new("a", "A", "main", 20, 5, 1, true, true),
    FullscreenPanel.new("b", "B", "side", 20, 5, 1, true, true),
]
val narrow = FullscreenLayoutState.new(FullscreenDimensions.new(70, 30), panels, [], "a", true, true, false, false, "")
expect(fullscreenLayoutMode(narrow.dimensions, false)).to_equal("stacked")
expect(fullscreenRegionFrames(narrow)[1].y).to_be_greater_than(fullscreenRegionFrames(narrow)[0].y)

step("Short terminals keep only the focused frame")
val short = FullscreenLayoutState.new(FullscreenDimensions.new(120, 20), panels, [], "b", true, true, false, false, "")
expect(fullscreenLayoutMode(short.dimensions, false)).to_equal("short")
expect(fullscreenRegionFrames(short).len()).to_equal(1)
expect(fullscreenRegionFrames(short)[0].id).to_equal("b")
```

</details>

#### models overlays, modal chrome hiding, and keyboard actions

- models overlays, modal chrome hiding, and keyboard actions
- Visible modal owns focus and blocks footer
   - Expected: fullscreenFocusRegion(state) equals `help`
   - Expected: fullscreenOverlayState(state) equals `modal:help`
   - Expected: fullscreenHeaderVisible(state) is false
   - Expected: fullscreenFooterVisible(state) is false
   - Expected: fullscreenOverlayFrame(state).id equals `help`
- Command palette overrides overlay focus
   - Expected: fullscreenFocusRegion(palette) equals `command-palette`
   - Expected: fullscreenOverlayState(palette) equals `command-palette`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models overlays, modal chrome hiding, and keyboard actions")
step("Visible modal owns focus and blocks footer")
val panels = [FullscreenPanel.new("main", "Main", "main", 20, 5, 1, true, true)]
val overlays = [FullscreenOverlay.new("help", "Help", "modal", true, true, true)]
val state = FullscreenLayoutState.new(FullscreenDimensions.new(100, 32), panels, overlays, "main", true, true, false, false, "")

expect(fullscreenFocusRegion(state)).to_equal("help")
expect(fullscreenOverlayState(state)).to_equal("modal:help")
expect(fullscreenHeaderVisible(state)).to_equal(false)
expect(fullscreenFooterVisible(state)).to_equal(false)
expect(fullscreenOverlayFrame(state).id).to_equal("help")
expect(fullscreenEnabledActionKeys(state)).to_contain("escape")
expect(fullscreenKeyboardSummary(state)[0]).to_contain("disabled")

step("Command palette overrides overlay focus")
val palette = FullscreenLayoutState.new(FullscreenDimensions.new(100, 32), panels, overlays, "main", true, true, false, true, "")
expect(fullscreenFocusRegion(palette)).to_equal("command-palette")
expect(fullscreenOverlayState(palette)).to_equal("command-palette")
```

</details>

#### renders summaries and source helpers

- renders summaries and source helpers
- Summaries expose stable parity strings
   - Expected: fullscreenResponsiveSummary(state) equals `compact layout, 1 panels, 0 overlays, focus main`
   - Expected: fullscreenSource() equals `FullscreenLayout`
   - Expected: fullscreenLayoutSourceLinesModeled() equals `636`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders summaries and source helpers")
step("Summaries expose stable parity strings")
val panels = [FullscreenPanel.new("main", "Main", "main", 20, 5, 1, true, true)]
val state = FullscreenLayoutState.new(FullscreenDimensions.new(100, 32), panels, [], "missing", true, true, true, false, "Idle")

expect(fullscreenResponsiveSummary(state)).to_equal("compact layout, 1 panels, 0 overlays, focus main")
expect(fullscreenLayoutSummary(state)[0]).to_contain("compact")
expect(fullscreenLayoutSummary(state)).to_contain("Idle")
expect(fullscreenSource()).to_equal("FullscreenLayout")
expect(fullscreenLayoutSourceLinesModeled()).to_equal(636)
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

- Canonical SPipe generation for source `525d03572bcb4d5f7b0941c24822f1e1ee8c077a544ddd7f748f3bfaab05cfd0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `525d03572bcb4d5f7b0941c24822f1e1ee8c077a544ddd7f748f3bfaab05cfd0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `525d03572bcb4d5f7b0941c24822f1e1ee8c077a544ddd7f748f3bfaab05cfd0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models wide layout dimensions and focus' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses stacked and short responsive modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/fullscreen_layout_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models overlays, modal chrome hiding, and keyboard actions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
