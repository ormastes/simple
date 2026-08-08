# Game2D SDN Assets (AC-6)

> `load_assets("...")` → `AssetTable` keyed by name. Missing path yields

<!-- sdn-diagram:id=game2d_sdn_assets_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_sdn_assets_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_sdn_assets_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_sdn_assets_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D SDN Assets (AC-6)

`load_assets("...")` → `AssetTable` keyed by name. Missing path yields

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_sdn_assets_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

`load_assets("...")` → `AssetTable` keyed by name. Missing path yields
`GAME-ASSET-001` carrying `file:line` from `parse_with_spans`. Wrong-type
asset (Sound where Image expected) → `GAME-ASSET-002`. Atlas region exceeds
image bounds → `GAME-ASSET-014`.

Fixtures:
- `test/fixtures/assets_ok.sdn` — happy-path declarations
- `test/fixtures/assets_missing.sdn` — references a missing path
- `test/fixtures/assets_wrong_type.sdn` — typed mismatch
- `test/fixtures/assets_atlas_oob.sdn` — out-of-bounds atlas region

Red-phase: AssetTable / load_assets absent; assertions fail until Phase 5.

## Scenarios

### Game2D SDN Assets (AC-6)
_## SDN-driven typed asset loader._

### AssetTable / AssetId / load_assets API

#### asset/table.spl declares fn load_assets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/table.spl")
expect(_has(src, "fn load_assets(")).to_equal(true)
```

</details>

#### asset/table.spl declares class AssetTable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/table.spl")
expect(_has(src, "class AssetTable")).to_equal(true)
```

</details>

#### asset/asset_id.spl declares class AssetId<T>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/asset_id.spl")
expect(_has(src, "class AssetId")).to_equal(true)
```

</details>

#### AssetTable.image/sound/font return Result<_, AssetError>

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/table.spl")
expect(_has(src, "Result<") and _has(src, "AssetError")
    ).to_equal(true)
```

</details>

#### diagnostic.spl declares class AssetError with code/file/line/key/msg

1.  has


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "class AssetError") and
       _has(src, "code") and _has(src, "file") and
       _has(src, "line") and _has(src, "key")).to_equal(true)
```

</details>

### happy-path fixture

#### test/fixtures/assets_ok.sdn exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(
    "test/fixtures/assets_ok.sdn")).to_equal(true)
```

</details>

#### assets_ok.sdn declares an image entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("test/fixtures/assets_ok.sdn")
expect(_has(src, "image") or _has(src, "Image")
    ).to_equal(true)
```

</details>

### edge case: missing-path diagnostic GAME-ASSET-001

#### test/fixtures/assets_missing.sdn exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(
    "test/fixtures/assets_missing.sdn")).to_equal(true)
```

</details>

#### diagnostic.spl wires GAME-ASSET-001

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "GAME-ASSET-001")).to_equal(true)
```

</details>

#### synthetic: detector matches the code form

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("error GAME-ASSET-001 missing image at file:line",
    "GAME-ASSET-001")).to_equal(true)
```

</details>

### error path: wrong-type asset GAME-ASSET-002

#### test/fixtures/assets_wrong_type.sdn exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(
    "test/fixtures/assets_wrong_type.sdn")).to_equal(true)
```

</details>

#### diagnostic.spl wires GAME-ASSET-002

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "GAME-ASSET-002")).to_equal(true)
```

</details>

### error path: atlas-OOB GAME-ASSET-014

#### test/fixtures/assets_atlas_oob.sdn exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(
    "test/fixtures/assets_atlas_oob.sdn")).to_equal(true)
```

</details>

#### diagnostic.spl wires GAME-ASSET-014

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "GAME-ASSET-014")).to_equal(true)
```

</details>

#### edge case: empty source does not falsely satisfy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("", "GAME-ASSET-014")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
