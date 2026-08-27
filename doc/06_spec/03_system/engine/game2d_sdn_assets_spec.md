# Game2D SDN Assets (AC-6)

> `load_assets("...")` → `AssetTable` keyed by name. Missing path yields

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
| Updated | 2026-08-26 |
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

### AssetTable / AssetId / load_assets API

#### asset/table.spl declares fn load_assets

- asset/table.spl declares fn load_assets
   - Expected: _has(src, "fn load_assets(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("asset/table.spl declares fn load_assets")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/table.spl")
expect(_has(src, "fn load_assets(")).to_equal(true)
```

</details>

#### asset/table.spl declares class AssetTable

- asset/table.spl declares class AssetTable
   - Expected: _has(src, "class AssetTable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("asset/table.spl declares class AssetTable")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/table.spl")
expect(_has(src, "class AssetTable")).to_equal(true)
```

</details>

#### asset/asset_id.spl declares class AssetId<T>

- asset/asset_id.spl declares class AssetId<T>
   - Expected: _has(src, "class AssetId") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("asset/asset_id.spl declares class AssetId<T>")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/asset_id.spl")
expect(_has(src, "class AssetId")).to_equal(true)
```

</details>

#### AssetTable.image/sound/font return Result<_, AssetError>

- AssetTable.image/sound/font return Result<_, AssetError>


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AssetTable.image/sound/font return Result<_, AssetError>")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/table.spl")
expect(_has(src, "Result<") and _has(src, "AssetError")
    ).to_equal(true)
```

</details>

#### diagnostic.spl declares class AssetError with code/file/line/key/msg

- diagnostic.spl declares class AssetError with code/file/line/key/msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic.spl declares class AssetError with code/file/line/key/msg")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "class AssetError") and
       _has(src, "code") and _has(src, "file") and
       _has(src, "line") and _has(src, "key")).to_equal(true)
```

</details>

### happy-path fixture

#### test/fixtures/assets_ok.sdn exists

- test/fixtures/assets_ok.sdn exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test/fixtures/assets_ok.sdn exists")
expect(rt_file_exists(
    "test/fixtures/assets_ok.sdn")).to_equal(true)
```

</details>

#### assets_ok.sdn declares an image entry

- assets_ok.sdn declares an image entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assets_ok.sdn declares an image entry")
val src = _read("test/fixtures/assets_ok.sdn")
expect(_has(src, "image") or _has(src, "Image")
    ).to_equal(true)
```

</details>

### edge case: missing-path diagnostic GAME-ASSET-001

#### test/fixtures/assets_missing.sdn exists

- test/fixtures/assets_missing.sdn exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test/fixtures/assets_missing.sdn exists")
expect(rt_file_exists(
    "test/fixtures/assets_missing.sdn")).to_equal(true)
```

</details>

#### diagnostic.spl wires GAME-ASSET-001

- diagnostic.spl wires GAME-ASSET-001
   - Expected: _has(src, "GAME-ASSET-001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic.spl wires GAME-ASSET-001")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "GAME-ASSET-001")).to_equal(true)
```

</details>

#### synthetic: detector matches the code form

- synthetic: detector matches the code form


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("synthetic: detector matches the code form")
expect(_has("error GAME-ASSET-001 missing image at file:line",
    "GAME-ASSET-001")).to_equal(true)
```

</details>

### error path: wrong-type asset GAME-ASSET-002

#### test/fixtures/assets_wrong_type.sdn exists

- test/fixtures/assets_wrong_type.sdn exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test/fixtures/assets_wrong_type.sdn exists")
expect(rt_file_exists(
    "test/fixtures/assets_wrong_type.sdn")).to_equal(true)
```

</details>

#### diagnostic.spl wires GAME-ASSET-002

- diagnostic.spl wires GAME-ASSET-002
   - Expected: _has(src, "GAME-ASSET-002") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic.spl wires GAME-ASSET-002")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "GAME-ASSET-002")).to_equal(true)
```

</details>

### error path: atlas-OOB GAME-ASSET-014

#### test/fixtures/assets_atlas_oob.sdn exists

- test/fixtures/assets_atlas_oob.sdn exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test/fixtures/assets_atlas_oob.sdn exists")
expect(rt_file_exists(
    "test/fixtures/assets_atlas_oob.sdn")).to_equal(true)
```

</details>

#### diagnostic.spl wires GAME-ASSET-014

- diagnostic.spl wires GAME-ASSET-014
   - Expected: _has(src, "GAME-ASSET-014") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic.spl wires GAME-ASSET-014")
val src = _read("src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl")
expect(_has(src, "GAME-ASSET-014")).to_equal(true)
```

</details>

#### edge case: empty source does not falsely satisfy

- edge case: empty source does not falsely satisfy
   - Expected: _has("", "GAME-ASSET-014") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: empty source does not falsely satisfy")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56820131e1d386edbc5e031357cb2258c22300a604c4fe016e5ff69ebfc3f155`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56820131e1d386edbc5e031357cb2258c22300a604c4fe016e5ff69ebfc3f155`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56820131e1d386edbc5e031357cb2258c22300a604c4fe016e5ff69ebfc3f155`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/game2d_sdn_assets_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_sdn_assets_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_sdn_assets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_sdn_assets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_sdn_assets_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'asset/table.spl declares fn load_assets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_sdn_assets_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'asset/table.spl declares class AssetTable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_sdn_assets_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'asset/asset_id.spl declares class AssetId<T>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
