# Claude Full Buddy Types

> Checks companion constants, rarity maps, and persisted companion DTO shapes.

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> std
types_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion constants, rarity maps, and persisted companion DTO shapes.

## Scenarios

### Claude full buddy types

#### exports companion inventories

- Pin rarity, species, eye, hat, and stat dimensions
   - Expected: rarities() equals `["common", "uncommon", "rare", "epic", "legendary"]`
   - Expected: speciesCount() equals `18`
   - Expected: rarityCount() equals `5`
   - Expected: eyeCount() equals `6`
   - Expected: hatCount() equals `8`
   - Expected: statCount() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Stored config persists soul and hatch time; bones are regenerated
   - Expected: companion.name equals `Pip`
   - Expected: companion.hatchedAt equals `42`
   - Expected: companion.bones.species equals `duck`
   - Expected: companion.bones.stats.snark equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
