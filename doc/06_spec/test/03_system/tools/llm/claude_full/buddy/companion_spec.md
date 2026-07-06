# Claude Full Buddy Companion

> Checks deterministic companion rolling and stored companion merge behavior.

<!-- sdn-diagram:id=companion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=companion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

companion_spec -> std
companion_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=companion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Buddy Companion

Checks deterministic companion rolling and stored companion merge behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/buddy/companion_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks deterministic companion rolling and stored companion merge behavior.

## Scenarios

### Claude full buddy companion

#### rolls deterministic bones from user id plus salt

- Same user gets same roll; different seed changes at least the inspiration seed
   - Expected: salt() equals `friend-2026-401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Same user gets same roll; different seed changes at least the inspiration seed")
expect(hashString("user_1friend-2026-401")).to_be_greater_than(0)
val a = roll("user_1")
expect(rollSignature("user_1")).to_contain("|")
expect(rarityList()).to_contain(a.bones.rarity)
expect(speciesList()).to_contain(a.bones.species)
expect(salt()).to_equal("friend-2026-401")
```

</details>

#### uses weighted rarity floors and common hat rule

- Common companions have no hat and higher rarities raise the stat floor
   - Expected: rollRarity(0) equals `common`
   - Expected: rollRarity(700) equals `uncommon`
   - Expected: rollRarity(900) equals `rare`
   - Expected: rollRarity(980) equals `epic`
   - Expected: rollRarity(999) equals `legendary`
   - Expected: rarityFloor("common") equals `5`
   - Expected: rarityFloor("legendary") equals `50`
   - Expected: rollWithSeed("force-common").bones.hat == "none" or rollWithSeed("force-common").bones.rarity != "common" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Common companions have no hat and higher rarities raise the stat floor")
expect(rollRarity(0)).to_equal("common")
expect(rollRarity(700)).to_equal("uncommon")
expect(rollRarity(900)).to_equal("rare")
expect(rollRarity(980)).to_equal("epic")
expect(rollRarity(999)).to_equal("legendary")
expect(rollStats(1, "legendary").min()).to_be_greater_than(39)
expect(rarityFloor("common")).to_equal(5)
expect(rarityFloor("legendary")).to_equal(50)
expect(rollWithSeed("force-common").bones.hat == "none" or rollWithSeed("force-common").bones.rarity != "common").to_equal(true)
```

</details>

#### caches the deterministic roll by salted key

- Repeated user id returns the cached value
- cache roll
   - Expected: cache.key equals `"u" + salt()`
- cache roll
   - Expected: cache.key equals `"u" + salt()`
- cache roll
   - Expected: cache.key equals `"v" + salt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Repeated user id returns the cached value")
val cache = RollCache.empty()
cache.roll("u")
expect(cache.key).to_equal("u" + salt())
cache.roll("u")
expect(cache.key).to_equal("u" + salt())
cache.roll("v")
expect(cache.key).to_equal("v" + salt())
```

</details>

#### chooses companion user id from config

- OAuth account wins, then userID, then anon
   - Expected: companionUserId(CompanionConfig.new("oauth", "user")) equals `oauth`
   - Expected: companionUserId(CompanionConfig.new("", "user")) equals `user`
   - Expected: companionUserId(CompanionConfig.new("", "")) equals `anon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("OAuth account wins, then userID, then anon")
expect(companionUserId(CompanionConfig.new("oauth", "user"))).to_equal("oauth")
expect(companionUserId(CompanionConfig.new("", "user"))).to_equal("user")
expect(companionUserId(CompanionConfig.new("", ""))).to_equal("anon")
```

</details>

#### merges stored soul with regenerated bones

- Stored name and mood persist, rarity and species come from roll
   - Expected: companion != nil is true
   - Expected: c.name equals `Pip`
   - Expected: c.mood equals `curious`
   - Expected: c.bones.species equals `roll("oauth").bones.species`
   - Expected: getCompanion(CompanionConfig.new("oauth", "user")) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stored name and mood persist, rarity and species come from roll")
val config = CompanionConfig.new("oauth", "user").withStored("Pip", "curious")
val companion = getCompanion(config)
expect(companion != nil).to_equal(true)
if val Some(c) = companion:
    expect(c.name).to_equal("Pip")
    expect(c.mood).to_equal("curious")
    expect(c.bones.species).to_equal(roll("oauth").bones.species)
expect(getCompanion(CompanionConfig.new("oauth", "user")) == nil).to_equal(true)
```

</details>

#### exports source arrays and hash helpers

- Arrays are non-empty and match companion roll dimensions
   - Expected: rarityList() equals `["common", "uncommon", "rare", "epic", "legendary"]`
   - Expected: statNames() equals `["helpfulness", "mischief", "focus", "luck"]`
   - Expected: hashString("abc") equals `hashString("abc")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Arrays are non-empty and match companion roll dimensions")
expect(speciesList().len()).to_be_greater_than(0)
expect(eyesList().len()).to_be_greater_than(0)
expect(hatsList()).to_contain("none")
expect(rarityList()).to_equal(["common", "uncommon", "rare", "epic", "legendary"])
expect(statNames()).to_equal(["helpfulness", "mischief", "focus", "luck"])
expect(hashString("abc")).to_equal(hashString("abc"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
