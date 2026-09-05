# Claude Full Buddy Sprites

> Checks companion sprite frame rendering, hats, faces, and species inventory.

<!-- sdn-diagram:id=sprites_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sprites_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sprites_spec -> std
sprites_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sprites_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Buddy Sprites

Checks companion sprite frame rendering, hats, faces, and species inventory.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/buddy/sprites_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion sprite frame rendering, hats, faces, and species inventory.

## Scenarios

### Claude full buddy sprites

#### renders body frames with eye substitution

- Duck frames wrap by modulo and remove blank hat row when safe
   - Expected: duck.len() equals `4`
   - Expected: renderSprite(SpriteBones.new("duck", "o", "none"), 3) equals `duck`
   - Expected: spriteFrameCount("duck") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Duck frames wrap by modulo and remove blank hat row when safe")
val duck = renderSprite(SpriteBones.new("duck", "o", "none"), 0)
expect(duck.len()).to_equal(4)
expect(duck[1]).to_contain("o")
expect(renderSprite(SpriteBones.new("duck", "o", "none"), 3)).to_equal(duck)
expect(spriteFrameCount("duck")).to_equal(3)
```

</details>

#### renders hats only into blank hat slots

- Hat appears on blank first line but fidget smoke keeps its row
   - Expected: duck[0] equals `hatLine("crown")`
   - Expected: hatLine("none") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hat appears on blank first line but fidget smoke keeps its row")
val duck = renderSprite(SpriteBones.new("duck", "o", "crown"), 0)
expect(duck[0]).to_equal(hatLine("crown"))
val dragon = renderSprite(SpriteBones.new("dragon", "o", "crown"), 2)
expect(dragon[0]).to_contain("~")
expect(hatLine("none")).to_equal("")
```

</details>

#### renders compact faces for each species branch

- Face output mirrors species-specific TypeScript switch
   - Expected: renderFace(SpriteBones.new("duck", "o", "none")) equals `(o>`
   - Expected: renderFace(SpriteBones.new("cat", "o", "none")) equals `=owo=`
   - Expected: renderFace(SpriteBones.new("dragon", "o", "none")) equals `<o~o>`
   - Expected: renderFace(SpriteBones.new("ghost", "o", "none")) equals `/oo\\`
   - Expected: renderFace(SpriteBones.new("robot", "o", "none")) equals `[oo]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Face output mirrors species-specific TypeScript switch")
expect(renderFace(SpriteBones.new("duck", "o", "none"))).to_equal("(o>")
expect(renderFace(SpriteBones.new("cat", "o", "none"))).to_equal("=owo=")
expect(renderFace(SpriteBones.new("dragon", "o", "none"))).to_equal("<o~o>")
expect(renderFace(SpriteBones.new("ghost", "o", "none"))).to_equal("/oo\\")
expect(renderFace(SpriteBones.new("robot", "o", "none"))).to_equal("[oo]")
```

</details>

#### exports species and hat inventories

- All source species have three idle frames
   - Expected: speciesList().len() equals `18`
   - Expected: hatList().len() equals `8`
   - Expected: allSpeciesHaveThreeFrames() is true
   - Expected: allRenderedSpritesHaveLines() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("All source species have three idle frames")
expect(speciesList().len()).to_equal(18)
expect(hatList().len()).to_equal(8)
expect(hatList()).to_contain("tinyduck")
expect(allSpeciesFrameCount()).to_be_greater_than(50)
expect(allSpeciesHaveThreeFrames()).to_equal(true)
expect(allRenderedSpritesHaveLines()).to_equal(true)
```

</details>

#### exports source-backed render constants

- Pin sprite dimensions and render rules
   - Expected: spriteHeight() equals `5`
   - Expected: spriteWidthAfterEyeSubstitution() equals `12`
   - Expected: hatSlotLineIndex() equals `0`
   - Expected: idleFrameCount() equals `3`
   - Expected: eyePlaceholder() equals `TS_EYE_PLACEHOLDER`
   - Expected: simpleEyePlaceholder() equals `@`
   - Expected: frameWrapsByModulo() is true
   - Expected: hatReplacesOnlyBlankSlot() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin sprite dimensions and render rules")
expect(spriteHeight()).to_equal(5)
expect(spriteWidthAfterEyeSubstitution()).to_equal(12)
expect(hatSlotLineIndex()).to_equal(0)
expect(idleFrameCount()).to_equal(3)
expect(eyePlaceholder()).to_equal("TS_EYE_PLACEHOLDER")
expect(simpleEyePlaceholder()).to_equal("@")
expect(bodyMapPurpose()).to_contain("idle fidget")
expect(blankHatSlotPurpose()).to_contain("blank line 0")
expect(frameWrapsByModulo()).to_equal(true)
expect(hatReplacesOnlyBlankSlot()).to_equal(true)
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
