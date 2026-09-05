# Claude Full Buddy Types

> Checks companion constants, rarity maps, and persisted companion DTO shapes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Buddy Types

Checks companion constants, rarity maps, and persisted companion DTO shapes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/buddy/types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion constants, rarity maps, and persisted companion DTO shapes.

## Scenarios

### Claude full buddy types

#### exports companion inventories

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports companion inventories
- Pin rarity, species, eye, hat, and stat dimensions
   - Expected: rarities() equals `["common", "uncommon", "rare", "epic", "legendary"]`
   - Expected: speciesCount() equals `18`
   - Expected: rarityCount() equals `5`
   - Expected: eyeCount() equals `6`
   - Expected: hatCount() equals `8`
   - Expected: statCount() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports companion inventories")
step("Pin rarity, species, eye, hat, and stat dimensions")
expect(rarities()).to_equal(["common", "uncommon", "rare", "epic", "legendary"])
expect(speciesCount()).to_equal(18)
expect(rarityCount()).to_equal(5)
expect(eyeCount()).to_equal(6)
expect(hatCount()).to_equal(8)
expect(statCount()).to_equal(5)
expect(species()).to_contain(duck())
expect(species()).to_contain(chonk())
expect(hats()).to_contain("tinyduck")
expect(statNames()).to_contain("SNARK")
```

</details>

#### exports rarity weights, stars, and theme colors

- exports rarity weights, stars, and theme colors
- Weights sum to 100 and colors match source theme keys
   - Expected: rarityWeight("common") equals `60`
   - Expected: rarityWeight("legendary") equals `1`
   - Expected: totalRarityWeight() equals `100`
   - Expected: rarityStars("rare") equals `***`
   - Expected: rarityStars("legendary") equals `*****`
   - Expected: rarityColor("common") equals `inactive`
   - Expected: rarityColor("uncommon") equals `success`
   - Expected: rarityColor("rare") equals `permission`
   - Expected: rarityColor("epic") equals `autoAccept`
   - Expected: rarityColor("legendary") equals `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports rarity weights, stars, and theme colors")
step("Weights sum to 100 and colors match source theme keys")
expect(rarityWeight("common")).to_equal(60)
expect(rarityWeight("legendary")).to_equal(1)
expect(totalRarityWeight()).to_equal(100)
expect(rarityStars("rare")).to_equal("***")
expect(rarityStars("legendary")).to_equal("*****")
expect(rarityColor("common")).to_equal("inactive")
expect(rarityColor("uncommon")).to_equal("success")
expect(rarityColor("rare")).to_equal("permission")
expect(rarityColor("epic")).to_equal("autoAccept")
expect(rarityColor("legendary")).to_equal("warning")
```

</details>

#### models companion bones and stored soul merge

- models companion bones and stored soul merge
- Stored config persists soul and hatch time; bones are regenerated
   - Expected: companion.name equals `Pip`
   - Expected: companion.hatchedAt equals `42`
   - Expected: companion.bones.species equals `duck`
   - Expected: companion.bones.stats.snark equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models companion bones and stored soul merge")
step("Stored config persists soul and hatch time; bones are regenerated")
val stats = CompanionStats.new(1, 2, 3, 4, 5)
val bones = CompanionBones.new(commonRarity(), duck(), "dot", "none", false, stats)
val stored = StoredCompanion.new("Pip", "curious", 42)
val companion = Companion.new(stored, bones)
expect(companion.name).to_equal("Pip")
expect(companion.hatchedAt).to_equal(42)
expect(companion.bones.species).to_equal("duck")
expect(companion.bones.stats.snark).to_equal(5)
```

</details>

#### exports persistence and source-shape invariants

- exports persistence and source-shape invariants
- Types distinguish regenerated bones from stored soul
   - Expected: storedCompanionPersistsBones() is false
   - Expected: companionBonesRegenerateFromUserHash() is true
   - Expected: speciesRuntimeConstructedInTypescript() is true
   - Expected: companionTypeIncludesSoulAndBones() is true
   - Expected: storedCompanionFieldCount() equals `3`
   - Expected: companionBonesFieldCount() equals `6`
   - Expected: legendaryRarity() equals `legendary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports persistence and source-shape invariants")
step("Types distinguish regenerated bones from stored soul")
expect(storedCompanionPersistsBones()).to_equal(false)
expect(companionBonesRegenerateFromUserHash()).to_equal(true)
expect(speciesRuntimeConstructedInTypescript()).to_equal(true)
expect(companionTypeIncludesSoulAndBones()).to_equal(true)
expect(storedCompanionFieldCount()).to_equal(3)
expect(companionBonesFieldCount()).to_equal(6)
expect(legendaryRarity()).to_equal("legendary")
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

- Canonical SPipe generation for source `993efb4354b9edeadcbf5968cf13069463f417aa32a21b96855711129a575dea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `993efb4354b9edeadcbf5968cf13069463f417aa32a21b96855711129a575dea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `993efb4354b9edeadcbf5968cf13069463f417aa32a21b96855711129a575dea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/buddy/types_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/buddy/types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/buddy/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/buddy/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/buddy/types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/buddy/types_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports companion inventories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/types_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports rarity weights, stars, and theme colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/types_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models companion bones and stored soul merge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
