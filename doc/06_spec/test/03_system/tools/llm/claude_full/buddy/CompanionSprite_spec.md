# Claude Full Buddy Companion Sprite

> Checks companion sprite layout, timing, and render-state decisions.

<!-- sdn-diagram:id=CompanionSprite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=CompanionSprite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

CompanionSprite_spec -> std
CompanionSprite_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=CompanionSprite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion sprite layout, timing, and render-state decisions.

## Scenarios

### Claude full buddy CompanionSprite

#### reserves columns only for visible full sprite

- Feature, companion, mute, and terminal width gates all apply
   - Expected: companionReservedColumns(config) equals `spriteColWidth(5) + spritePaddingX()`
   - Expected: companionReservedColumns(config) equals `spriteColWidth(5) + spritePaddingX() + bubbleWidth()`
   - Expected: companionReservedColumns(config) equals `spriteColWidth(5) + spritePaddingX()`
   - Expected: companionReservedColumns(config) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Narrow mode quotes reaction quips and does not reserve columns
   - Expected: rendered.visible is true
   - Expected: rendered.mode equals `narrow`
   - Expected: rendered.reservedColumns equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Full-width scrollback renders inline bubble beside the sprite
   - Expected: rendered.mode equals `inline-bubble`
   - Expected: rendered.bubbleTail equals `right`
   - Expected: rendered.fading is true
   - Expected: fullscreen.mode equals `fullscreen-sprite-only`
   - Expected: fullscreen.bubbleTail equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Idle sentinel blinks, reaction and petting cycle frames
   - Expected: companionSpriteFrame(false, false, 8, 3) equals `0`
   - Expected: companionShouldBlink(false, false, 8) is true
   - Expected: companionSpriteFrame(true, false, 5, 3) equals `2`
   - Expected: companionSpriteFrame(false, true, 4, 3) equals `1`
   - Expected: isPetting(4, 0, 10) is true
   - Expected: isPetting(5, 0, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Floating bubble uses a down tail and hides when muted or empty
   - Expected: bubble.visible is true
   - Expected: bubble.mode equals `floating-bubble`
   - Expected: bubble.bubbleTail equals `down`
   - Expected: bubble.fading is true
   - Expected: renderFloatingBubble(config).visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
