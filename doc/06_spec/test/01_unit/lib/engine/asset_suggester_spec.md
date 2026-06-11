# Asset Suggester Specification

> <details>

<!-- sdn-diagram:id=asset_suggester_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=asset_suggester_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

asset_suggester_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=asset_suggester_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Asset Suggester Specification

## Scenarios

### AssetEntry

#### creates an asset entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val asset = AssetEntry.new("hero", "texture", "assets/hero.png")
expect(asset.name).to_equal("hero")
expect(asset.category).to_equal("texture")
expect(asset.path).to_equal("assets/hero.png")
```

</details>

#### adds and checks tags

1. var asset = AssetEntry new
2. asset add tag
3. asset add tag
   - Expected: asset.has_tag("weapon") is true
   - Expected: asset.has_tag("melee") is true
   - Expected: asset.has_tag("ranged") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var asset = AssetEntry.new("sword", "model", "assets/sword.obj")
asset.add_tag("weapon")
asset.add_tag("melee")
expect(asset.has_tag("weapon")).to_equal(true)
expect(asset.has_tag("melee")).to_equal(true)
expect(asset.has_tag("ranged")).to_equal(false)
```

</details>

### AssetSuggester

#### starts empty

1. var suggester = AssetSuggester new
   - Expected: suggester.catalog_size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
expect(suggester.catalog_size()).to_equal(0)
```

</details>

#### adds assets to catalog

1. var suggester = AssetSuggester new
2. var a1 = AssetEntry new
3. var a2 = AssetEntry new
4. suggester add asset
5. suggester add asset
   - Expected: suggester.catalog_size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
var a1 = AssetEntry.new("hero", "texture", "assets/hero.png")
var a2 = AssetEntry.new("tree", "model", "assets/tree.obj")
suggester.add_asset(a1)
suggester.add_asset(a2)
expect(suggester.catalog_size()).to_equal(2)
```

</details>

#### searches by tag

1. var suggester = AssetSuggester new
2. var a1 = AssetEntry new
3. a1 add tag
4. a1 add tag
5. var a2 = AssetEntry new
6. a2 add tag
7. var a3 = AssetEntry new
8. a3 add tag
9. suggester add asset
10. suggester add asset
11. suggester add asset
   - Expected: results.len().to_i32() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
var a1 = AssetEntry.new("hero_sprite", "texture", "assets/hero.png")
a1.add_tag("character")
a1.add_tag("player")
var a2 = AssetEntry.new("tree_model", "model", "assets/tree.obj")
a2.add_tag("environment")
var a3 = AssetEntry.new("enemy_sprite", "texture", "assets/enemy.png")
a3.add_tag("character")
suggester.add_asset(a1)
suggester.add_asset(a2)
suggester.add_asset(a3)
val results = suggester.search_by_tag("character")
expect(results.len().to_i32()).to_equal(2)
```

</details>

#### searches by category

1. var suggester = AssetSuggester new
2. var a1 = AssetEntry new
3. var a2 = AssetEntry new
4. var a3 = AssetEntry new
5. suggester add asset
6. suggester add asset
7. suggester add asset
   - Expected: results.len().to_i32() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
var a1 = AssetEntry.new("hero", "texture", "assets/hero.png")
var a2 = AssetEntry.new("tree", "model", "assets/tree.obj")
var a3 = AssetEntry.new("bg", "texture", "assets/bg.png")
suggester.add_asset(a1)
suggester.add_asset(a2)
suggester.add_asset(a3)
val results = suggester.search_by_category("texture")
expect(results.len().to_i32()).to_equal(2)
```

</details>

#### searches by name substring

1. var suggester = AssetSuggester new
2. var a1 = AssetEntry new
3. var a2 = AssetEntry new
4. var a3 = AssetEntry new
5. suggester add asset
6. suggester add asset
7. suggester add asset
   - Expected: results.len().to_i32() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
var a1 = AssetEntry.new("hero_sprite", "texture", "assets/hero.png")
var a2 = AssetEntry.new("hero_idle", "animation", "assets/hero_idle.anim")
var a3 = AssetEntry.new("tree_model", "model", "assets/tree.obj")
suggester.add_asset(a1)
suggester.add_asset(a2)
suggester.add_asset(a3)
val results = suggester.search_by_name("hero")
expect(results.len().to_i32()).to_equal(2)
```

</details>

#### returns empty for no matches

1. var suggester = AssetSuggester new
2. var a1 = AssetEntry new
3. suggester add asset
   - Expected: results.len().to_i32() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
var a1 = AssetEntry.new("hero", "texture", "assets/hero.png")
suggester.add_asset(a1)
val results = suggester.search_by_tag("nonexistent")
expect(results.len().to_i32()).to_equal(0)
```

</details>

#### suggests with relevance scores

1. var suggester = AssetSuggester new
2. var a1 = AssetEntry new
3. a1 add tag
4. var a2 = AssetEntry new
5. a2 add tag
6. var a3 = AssetEntry new
7. a3 add tag
8. suggester add asset
9. suggester add asset
10. suggester add asset
   - Expected: suggestions.len().to_i32() equals `2`
   - Expected: suggestions[0].relevance equals `1.0`
   - Expected: suggestions[0].asset.name equals `fire_spell`
   - Expected: suggestions[1].relevance equals `0.5`
   - Expected: suggestions[1].asset.name equals `fire_ball`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
var a1 = AssetEntry.new("fire_spell", "effect", "assets/fire.fx")
a1.add_tag("fire")
var a2 = AssetEntry.new("fire_ball", "projectile", "assets/fireball.obj")
a2.add_tag("projectile")
var a3 = AssetEntry.new("ice_spell", "effect", "assets/ice.fx")
a3.add_tag("ice")
suggester.add_asset(a1)
suggester.add_asset(a2)
suggester.add_asset(a3)

val suggestions = suggester.suggest("fire")
# a1 matches by tag (relevance 1.0), a2 matches by name (relevance 0.5)
expect(suggestions.len().to_i32()).to_equal(2)
expect(suggestions[0].relevance).to_equal(1.0)
expect(suggestions[0].asset.name).to_equal("fire_spell")
expect(suggestions[1].relevance).to_equal(0.5)
expect(suggestions[1].asset.name).to_equal("fire_ball")
```

</details>

#### deduplicates tag and name matches in suggest

1. var suggester = AssetSuggester new
2. var a1 = AssetEntry new
3. a1 add tag
4. suggester add asset
   - Expected: suggestions.len().to_i32() equals `1`
   - Expected: suggestions[0].relevance equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suggester = AssetSuggester.new()
var a1 = AssetEntry.new("fire_effect", "effect", "assets/fire.fx")
a1.add_tag("fire")
suggester.add_asset(a1)

# "fire" matches both tag and name; should appear only once with tag relevance
val suggestions = suggester.suggest("fire")
expect(suggestions.len().to_i32()).to_equal(1)
expect(suggestions[0].relevance).to_equal(1.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/asset_suggester_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AssetEntry
- AssetSuggester

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
