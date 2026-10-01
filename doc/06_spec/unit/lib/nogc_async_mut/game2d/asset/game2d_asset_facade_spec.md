# Game2d Asset Facade Specification

> Tests covering nogc_async_mut game2d asset facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Asset Facade Specification

## Scenarios

### nogc_async_mut game2d asset facade

#### re-exports typed ids, diagnostics, and empty asset table behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports typed ids, diagnostics, and empty asset table behavior
   - Expected: valid.key equals `hero`
   - Expected: valid.raw equals `1`
   - Expected: valid.is_valid() is true
   - Expected: valid.eq(AssetId<text>.new("hero", 1)) is true
   - Expected: err.code equals `GAME-ASSET-001`
   - Expected: atlas.image_width equals `64`
   - Expected: table.images.len() equals `0`
   - Expected: table.sounds.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports typed ids, diagnostics, and empty asset table behavior")
val valid = AssetId<text>.new("hero", 1)
expect(valid.key).to_equal("hero")
expect(valid.raw).to_equal(1)
expect(valid.is_valid()).to_equal(true)
expect(valid.eq(AssetId<text>.new("hero", 1))).to_equal(true)
val err = AssetError.missing(Span(line: 7, column: 3), "assets.sdn", "hero")
expect(err.code).to_equal("GAME-ASSET-001")
expect(err.diagnostic()).to_contain("hero")
val atlas = Atlas.new("sprites", 64, 32)
expect(atlas.image_width).to_equal(64)
val table = AssetTable.empty()
expect(table.images.len()).to_equal(0)
expect(table.sounds.keys().len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut game2d asset facade.
- nogc_async_mut game2d asset facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c10adaf941756abe8a3a9e12b53aacfcfd096cdb1787479e9c9edc5bf9e89b8d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c10adaf941756abe8a3a9e12b53aacfcfd096cdb1787479e9c9edc5bf9e89b8d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c10adaf941756abe8a3a9e12b53aacfcfd096cdb1787479e9c9edc5bf9e89b8d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports typed ids, diagnostics, and empty asset table behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
