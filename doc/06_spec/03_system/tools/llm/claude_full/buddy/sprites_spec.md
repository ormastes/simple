# Claude Full Buddy Sprites

> Checks companion sprite frame rendering, hats, faces, and species inventory.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion sprite frame rendering, hats, faces, and species inventory.

## Scenarios

### Claude full buddy sprites

#### renders body frames with eye substitution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders body frames with eye substitution
- Duck frames wrap by modulo and remove blank hat row when safe
   - Expected: duck.len() equals `4`
   - Expected: renderSprite(SpriteBones.new("duck", "o", "none"), 3) equals `duck`
   - Expected: spriteFrameCount("duck") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders body frames with eye substitution")
step("Duck frames wrap by modulo and remove blank hat row when safe")
val duck = renderSprite(SpriteBones.new("duck", "o", "none"), 0)
expect(duck.len()).to_equal(4)
expect(duck[1]).to_contain("o")
expect(renderSprite(SpriteBones.new("duck", "o", "none"), 3)).to_equal(duck)
expect(spriteFrameCount("duck")).to_equal(3)
```

</details>

#### renders hats only into blank hat slots

- renders hats only into blank hat slots
- Hat appears on blank first line but fidget smoke keeps its row
   - Expected: duck[0] equals `hatLine("crown")`
   - Expected: hatLine("none") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders hats only into blank hat slots")
step("Hat appears on blank first line but fidget smoke keeps its row")
val duck = renderSprite(SpriteBones.new("duck", "o", "crown"), 0)
expect(duck[0]).to_equal(hatLine("crown"))
val dragon = renderSprite(SpriteBones.new("dragon", "o", "crown"), 2)
expect(dragon[0]).to_contain("~")
expect(hatLine("none")).to_equal("")
```

</details>

#### renders compact faces for each species branch

- renders compact faces for each species branch
- Face output mirrors species-specific TypeScript switch
   - Expected: renderFace(SpriteBones.new("duck", "o", "none")) equals `(o>`
   - Expected: renderFace(SpriteBones.new("cat", "o", "none")) equals `=owo=`
   - Expected: renderFace(SpriteBones.new("dragon", "o", "none")) equals `<o~o>`
   - Expected: renderFace(SpriteBones.new("ghost", "o", "none")) equals `/oo\\`
   - Expected: renderFace(SpriteBones.new("robot", "o", "none")) equals `[oo]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders compact faces for each species branch")
step("Face output mirrors species-specific TypeScript switch")
expect(renderFace(SpriteBones.new("duck", "o", "none"))).to_equal("(o>")
expect(renderFace(SpriteBones.new("cat", "o", "none"))).to_equal("=owo=")
expect(renderFace(SpriteBones.new("dragon", "o", "none"))).to_equal("<o~o>")
expect(renderFace(SpriteBones.new("ghost", "o", "none"))).to_equal("/oo\\")
expect(renderFace(SpriteBones.new("robot", "o", "none"))).to_equal("[oo]")
```

</details>

#### exports species and hat inventories

- exports species and hat inventories
- All source species have three idle frames
   - Expected: speciesList().len() equals `18`
   - Expected: hatList().len() equals `8`
   - Expected: allSpeciesHaveThreeFrames() is true
   - Expected: allRenderedSpritesHaveLines() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports species and hat inventories")
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

- exports source-backed render constants
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

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed render constants")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `18b479aa604ee591c371bfea7dbac0bc704fdc2f6ae84a6ac7c7f5a10dc4aa7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18b479aa604ee591c371bfea7dbac0bc704fdc2f6ae84a6ac7c7f5a10dc4aa7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18b479aa604ee591c371bfea7dbac0bc704fdc2f6ae84a6ac7c7f5a10dc4aa7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/buddy/sprites_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/buddy/sprites_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/buddy/sprites_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/buddy/sprites_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/buddy/sprites_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/buddy/sprites_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders body frames with eye substitution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/sprites_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders hats only into blank hat slots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/sprites_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders compact faces for each species branch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
