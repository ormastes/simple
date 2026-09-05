# Claude Full Buddy Companion

> Checks deterministic companion rolling and stored companion merge behavior.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks deterministic companion rolling and stored companion merge behavior.

## Scenarios

### Claude full buddy companion

#### rolls deterministic bones from user id plus salt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rolls deterministic bones from user id plus salt
- Same user gets same roll; different seed changes at least the inspiration seed
   - Expected: salt() equals `friend-2026-401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rolls deterministic bones from user id plus salt")
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

- uses weighted rarity floors and common hat rule
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

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses weighted rarity floors and common hat rule")
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

- caches the deterministic roll by salted key
- Repeated user id returns the cached value
   - Expected: cache.key equals `"u" + salt()`
   - Expected: cache.key equals `"u" + salt()`
   - Expected: cache.key equals `"v" + salt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caches the deterministic roll by salted key")
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

- chooses companion user id from config
- OAuth account wins, then userID, then anon
   - Expected: companionUserId(CompanionConfig.new("oauth", "user")) equals `oauth`
   - Expected: companionUserId(CompanionConfig.new("", "user")) equals `user`
   - Expected: companionUserId(CompanionConfig.new("", "")) equals `anon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chooses companion user id from config")
step("OAuth account wins, then userID, then anon")
expect(companionUserId(CompanionConfig.new("oauth", "user"))).to_equal("oauth")
expect(companionUserId(CompanionConfig.new("", "user"))).to_equal("user")
expect(companionUserId(CompanionConfig.new("", ""))).to_equal("anon")
```

</details>

#### merges stored soul with regenerated bones

- merges stored soul with regenerated bones
- Stored name and mood persist, rarity and species come from roll
   - Expected: c.name equals `Pip`
   - Expected: c.mood equals `curious`
   - Expected: c.bones.species equals `roll("oauth").bones.species`
   - Expected: getCompanion(CompanionConfig.new("oauth", "user")) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("merges stored soul with regenerated bones")
step("Stored name and mood persist, rarity and species come from roll")
val config = CompanionConfig.new("oauth", "user").withStored("Pip", "curious")
val companion = getCompanion(config)
assert_not_equal(companion, nil)
if val Some(c) = companion:
    expect(c.name).to_equal("Pip")
    expect(c.mood).to_equal("curious")
    expect(c.bones.species).to_equal(roll("oauth").bones.species)
expect(getCompanion(CompanionConfig.new("oauth", "user"))).to_equal(nil)
```

</details>

#### exports source arrays and hash helpers

- exports source arrays and hash helpers
- Arrays are non-empty and match companion roll dimensions
   - Expected: rarityList() equals `["common", "uncommon", "rare", "epic", "legendary"]`
   - Expected: statNames() equals `["helpfulness", "mischief", "focus", "luck"]`
   - Expected: hashString("abc") equals `hashString("abc")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source arrays and hash helpers")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `95def828811d924dccbdcc86a92d8e9287c8da94cae484e0874a89a628b951a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95def828811d924dccbdcc86a92d8e9287c8da94cae484e0874a89a628b951a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95def828811d924dccbdcc86a92d8e9287c8da94cae484e0874a89a628b951a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/buddy/companion_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/buddy/companion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/buddy/companion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/buddy/companion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/buddy/companion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/buddy/companion_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rolls deterministic bones from user id plus salt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/companion_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses weighted rarity floors and common hat rule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/companion_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches the deterministic roll by salted key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
