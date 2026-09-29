# Claude Full Buddy Companion Sprite

> Checks companion sprite layout, timing, and render-state decisions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Buddy Companion Sprite

Checks companion sprite layout, timing, and render-state decisions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion sprite layout, timing, and render-state decisions.

## Scenarios

### Claude full buddy CompanionSprite

#### reserves columns only for visible full sprite

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reserves columns only for visible full sprite
- Feature, companion, mute, and terminal width gates all apply
   - Expected: companionReservedColumns(config) equals `spriteColWidth(5) + spritePaddingX()`
   - Expected: companionReservedColumns(config) equals `spriteColWidth(5) + spritePaddingX() + bubbleWidth()`
   - Expected: companionReservedColumns(config) equals `spriteColWidth(5) + spritePaddingX()`
   - Expected: companionReservedColumns(config) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reserves columns only for visible full sprite")
step("Feature, companion, mute, and terminal width gates all apply")
val config = CompanionSpriteConfig.basic("Buddy", 120)
expect(companionReservedColumns(config)).to_equal(spriteColWidth(5) + spritePaddingX())
config.speaking = true
expect(companionReservedColumns(config)).to_equal(spriteColWidth(5) + spritePaddingX() + bubbleWidth())
config.fullscreen = true
expect(companionReservedColumns(config)).to_equal(spriteColWidth(5) + spritePaddingX())
config.terminalColumns = 80
expect(companionReservedColumns(config)).to_equal(0)
```

</details>

#### renders narrow terminals as one line

- renders narrow terminals as one line
- Narrow mode quotes reaction quips and does not reserve columns
   - Expected: rendered.visible is true
   - Expected: rendered.mode equals `narrow`
   - Expected: rendered.reservedColumns equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders narrow terminals as one line")
step("Narrow mode quotes reaction quips and does not reserve columns")
val config = CompanionSpriteConfig.basic("Buddy", 70)
config.reaction = "hello there from a very long buddy message"
config.focused = true
val rendered = renderCompanionSprite(config)
expect(rendered.visible).to_equal(true)
expect(rendered.mode).to_equal("narrow")
expect(rendered.reservedColumns).to_equal(0)
expect(rendered.label).to_start_with("\"")
expect(rendered.label).to_contain("...")
```

</details>

#### renders full sprite and inline bubble modes

- renders full sprite and inline bubble modes
- Full-width scrollback renders inline bubble beside the sprite
   - Expected: rendered.mode equals `inline-bubble`
   - Expected: rendered.bubbleTail equals `right`
   - Expected: rendered.fading is true
   - Expected: fullscreen.mode equals `fullscreen-sprite-only`
   - Expected: fullscreen.bubbleTail equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders full sprite and inline bubble modes")
step("Full-width scrollback renders inline bubble beside the sprite")
val config = CompanionSpriteConfig.basic("Buddy", 120)
config.reaction = "nice work"
config.speaking = true
config.tick = 15
config.lastSpokeTick = 0
val rendered = renderCompanionSprite(config)
expect(rendered.mode).to_equal("inline-bubble")
expect(rendered.bubbleTail).to_equal("right")
expect(rendered.fading).to_equal(true)
config.fullscreen = true
val fullscreen = renderCompanionSprite(config)
expect(fullscreen.mode).to_equal("fullscreen-sprite-only")
expect(fullscreen.bubbleTail).to_equal("")
```

</details>

#### computes idle, blink, excited, and pet frames

- computes idle, blink, excited, and pet frames
- Idle sentinel blinks, reaction and petting cycle frames
   - Expected: companionSpriteFrame(false, false, 8, 3) equals `0`
   - Expected: companionShouldBlink(false, false, 8) is true
   - Expected: companionSpriteFrame(true, false, 5, 3) equals `2`
   - Expected: companionSpriteFrame(false, true, 4, 3) equals `1`
   - Expected: isPetting(4, 0, 10) is true
   - Expected: isPetting(5, 0, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes idle, blink, excited, and pet frames")
step("Idle sentinel blinks, reaction and petting cycle frames")
expect(companionSpriteFrame(false, false, 8, 3)).to_equal(0)
expect(companionShouldBlink(false, false, 8)).to_equal(true)
expect(companionSpriteFrame(true, false, 5, 3)).to_equal(2)
expect(companionSpriteFrame(false, true, 4, 3)).to_equal(1)
expect(isPetting(4, 0, 10)).to_equal(true)
expect(isPetting(5, 0, 10)).to_equal(false)
expect(petHeartFrame(4)).to_contain("dot")
```

</details>

#### renders floating bubble for fullscreen overlay

- renders floating bubble for fullscreen overlay
- Floating bubble uses a down tail and hides when muted or empty
   - Expected: bubble.visible is true
   - Expected: bubble.mode equals `floating-bubble`
   - Expected: bubble.bubbleTail equals `down`
   - Expected: bubble.fading is true
   - Expected: renderFloatingBubble(config).visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders floating bubble for fullscreen overlay")
step("Floating bubble uses a down tail and hides when muted or empty")
val config = CompanionSpriteConfig.basic("Buddy", 120)
config.reaction = "floating words wrap here"
config.tick = 14
val bubble = renderFloatingBubble(config)
expect(bubble.visible).to_equal(true)
expect(bubble.mode).to_equal("floating-bubble")
expect(bubble.bubbleTail).to_equal("down")
expect(bubble.fading).to_equal(true)
config.reaction = ""
expect(renderFloatingBubble(config).visible).to_equal(false)
```

</details>

#### wraps speech and exposes timing constants

- wraps speech and exposes timing constants
- Bubble helpers preserve source timing and wrapping behavior
   - Expected: wrapText("one two three four", 8) equals `["one two", "three", "four"]`
   - Expected: bubbleFading("hi", 14, 0) is true
   - Expected: narrowQuip("abcdefghijklmnopqrstuvwxyz") equals `abcdefghijklmnopqrstuvw...`
   - Expected: speechBubbleBorderColor("primary", true) equals `inactive`
   - Expected: speechBubbleTailShape("right") equals `horizontal`
   - Expected: speechBubbleTailShape("down") equals `diagonal`
   - Expected: reactionClearAfterMs() equals `10000`
   - Expected: floatingBubbleTickResetsOnReactionChange("a", "b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps speech and exposes timing constants")
step("Bubble helpers preserve source timing and wrapping behavior")
expect(wrapText("one two three four", 8)).to_equal(["one two", "three", "four"])
expect(bubbleFading("hi", 14, 0)).to_equal(true)
expect(narrowQuip("abcdefghijklmnopqrstuvwxyz")).to_equal("abcdefghijklmnopqrstuvw...")
expect(speechBubbleBorderColor("primary", true)).to_equal("inactive")
expect(speechBubbleTailShape("right")).to_equal("horizontal")
expect(speechBubbleTailShape("down")).to_equal("diagonal")
expect(reactionClearAfterMs()).to_equal(10000)
expect(floatingBubbleTickResetsOnReactionChange("a", "b")).to_equal(true)
```

</details>

#### exports source-backed constants

- exports source-backed constants
- Pin constants and render contracts
   - Expected: minColsForFullSprite() equals `100`
   - Expected: tickMs() equals `500`
   - Expected: bubbleShowTicks() equals `20`
   - Expected: fadeWindowTicks() equals `6`
   - Expected: petBurstMs() equals `2500`
   - Expected: spriteBodyWidth() equals `12`
   - Expected: nameRowPad() equals `2`
   - Expected: bubbleWidth() equals `36`
   - Expected: narrowQuipCap() equals `24`
   - Expected: speechWrapWidth() equals `30`
   - Expected: speechBubbleBoxWidth() equals `34`
   - Expected: idleSequenceLength() equals `15`
   - Expected: petHeartFrameCount() equals `5`
   - Expected: heartGlyph() equals `HEART`
   - Expected: bubbleShowApproxSeconds() equals `10`
   - Expected: fadeWindowApproxSeconds() equals `3`
   - Expected: spriteUsesInlineBubbleInScrollback() is true
   - Expected: spriteUsesFloatingBubbleInFullscreen() is true
   - Expected: narrowModeUsesNoReservation() is true
   - Expected: companionSpriteSourceLinesModeled() equals `370`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
step("Pin constants and render contracts")
expect(minColsForFullSprite()).to_equal(100)
expect(tickMs()).to_equal(500)
expect(bubbleShowTicks()).to_equal(20)
expect(fadeWindowTicks()).to_equal(6)
expect(petBurstMs()).to_equal(2500)
expect(spriteBodyWidth()).to_equal(12)
expect(nameRowPad()).to_equal(2)
expect(bubbleWidth()).to_equal(36)
expect(narrowQuipCap()).to_equal(24)
expect(speechWrapWidth()).to_equal(30)
expect(speechBubbleBoxWidth()).to_equal(34)
expect(idleSequenceLength()).to_equal(15)
expect(petHeartFrameCount()).to_equal(5)
expect(heartGlyph()).to_equal("HEART")
expect(bubbleShowApproxSeconds()).to_equal(10)
expect(fadeWindowApproxSeconds()).to_equal(3)
expect(spriteUsesInlineBubbleInScrollback()).to_equal(true)
expect(spriteUsesFloatingBubbleInFullscreen()).to_equal(true)
expect(narrowModeUsesNoReservation()).to_equal(true)
expect(companionSpriteSourceLinesModeled()).to_equal(370)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `eb69e1bc64e4ee27fc5ebab7b933e6c71a743b4ae3ba2705a225d5abc14c4319`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb69e1bc64e4ee27fc5ebab7b933e6c71a743b4ae3ba2705a225d5abc14c4319`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb69e1bc64e4ee27fc5ebab7b933e6c71a743b4ae3ba2705a225d5abc14c4319`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reserves columns only for visible full sprite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders narrow terminals as one line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/CompanionSprite_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders full sprite and inline bubble modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
