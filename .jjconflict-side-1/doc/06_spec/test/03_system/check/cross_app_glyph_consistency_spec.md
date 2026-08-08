# Cross-App Glyph Consistency (Browser vs GUI Showcase)

> Verifies gate G2.5: "the browser and the GUI showcase render shared UI chrome ... with identical glyph rasterization and theme tokens (cross-app pixel oracle over shared widgets)."

<!-- sdn-diagram:id=cross_app_glyph_consistency_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cross_app_glyph_consistency_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cross_app_glyph_consistency_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cross_app_glyph_consistency_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross-App Glyph Consistency (Browser vs GUI Showcase)

Verifies gate G2.5: "the browser and the GUI showcase render shared UI chrome ... with identical glyph rasterization and theme tokens (cross-app pixel oracle over shared widgets)."

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | G2.5 |
| Category | Testing \| Infrastructure \| GUI |
| Status | Done |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G2.5) |
| Design | N/A |
| Source | `test/03_system/check/cross_app_glyph_consistency_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies gate G2.5: "the browser and the GUI showcase render shared UI chrome
... with identical glyph rasterization and theme tokens (cross-app pixel
oracle over shared widgets)."

Both text paths now share ONE 5x7 bitmap table
(`src/lib/common/ui/glyph_bitmap_5x7.spl`):

1. **GUI showcase path:** `std.gpu.engine2d.backend_software.SoftwareBackend
   .draw_text()`, backed by `std.gpu.engine2d.glyph.glyph_data()`, which
   delegates to the shared table.
2. **Browser path:** the pure-Simple web layout renderer
   (`simple_web_html_layout_renderer.spl`), whose `glyph_row_bits` /
   `glyph_index_for_char_code` are imported from the same shared table.

`scripts/check/check-cross-app-glyph-consistency.shs` proves identity two ways:
a rendered per-character pixel oracle over `AEFHSVXYZ` (each char on its own
canvas per app, tight-ink-box diffed) with zero mismatches, and a source-level
comparison across the full 88-char charset (`strict_mismatched_pixels=0`). The
per-character advance is unified at `5*scale` on both sides
(Engine2D `glyph_advance`, browser `text_advance`).

History: the two paths formerly used independently authored tables (41/88
identical, 47/88 divergent) and differing advances (6*scale vs 5*scale),
tracked as
doc/08_tracking/bug/cross_app_glyph_rasterization_diverges_2026-07-02.md
(now fixed).

Per the test_runner_masks_child_and_expectation_failures bug (see the
Browser Interaction spec), the authoritative gate is the check script's own
grep-based exit; this spec asserts on the persisted evidence contents.

## Related Specifications

- [Production Readiness Master Plan](../../../doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md) — G2.5
- [Browser Interaction Capture Evidence](../gui/browser_interaction_spec.spl)
- [GUI Low-Res Readability](gui_low_res_readability_spec.spl)

## Scenarios

### Cross-App Glyph Consistency (Browser vs GUI Showcase)

#### cross-app glyph consistency check produced evidence

- print "Loaded evidence with {entries len
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()
```

</details>

#### capture+compare infrastructure ran successfully

- print "Loaded evidence with {entries len
   - Expected: get_env_value(entries, "driver_status") equals `pass`
   - Expected: get_env_value(entries, "overall") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "driver_status")).to_equal("pass")
    expect(get_env_value(entries, "overall")).to_equal("pass")
```

</details>

#### anchor glyphs 'A' and 'Z' render byte-identical ink in both apps

- print "Loaded evidence with {entries len
   - Expected: get_env_value(entries, "char_0_glyph") equals `A`
   - Expected: get_env_value(entries, "char_0_status") equals `match`
   - Expected: get_env_value(entries, "char_0_mismatch_px") equals `0`
   - Expected: get_env_value(entries, "char_8_glyph") equals `Z`
   - Expected: get_env_value(entries, "char_8_status") equals `match`
   - Expected: get_env_value(entries, "char_8_mismatch_px") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "char_0_glyph")).to_equal("A")
    expect(get_env_value(entries, "char_0_status")).to_equal("match")
    expect(get_env_value(entries, "char_0_mismatch_px")).to_equal("0")
    expect(get_env_value(entries, "char_8_glyph")).to_equal("Z")
    expect(get_env_value(entries, "char_8_status")).to_equal("match")
    expect(get_env_value(entries, "char_8_mismatch_px")).to_equal("0")
```

</details>

#### G2.5 closed: both paths rasterize byte-identically (no divergence)

- print "Loaded evidence with {entries len
   - Expected: get_env_value(entries, "glyph_consistency_status") equals `identical`
   - Expected: get_env_value(entries, "diverging_chars") equals `0`
   - Expected: get_env_value(entries, "char_1_glyph") equals `E`
   - Expected: get_env_value(entries, "char_1_status") equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    # Both text paths now share one 5x7 table
    # (common.ui.glyph_bitmap_5x7), so rasterization is identical.
    expect(get_env_value(entries, "glyph_consistency_status")).to_equal("identical")
    expect(get_env_value(entries, "diverging_chars")).to_equal("0")
    expect(get_env_value(entries, "char_1_glyph")).to_equal("E")
    expect(get_env_value(entries, "char_1_status")).to_equal("match")
```

</details>

#### rendered per-char oracle has zero mismatched pixels

- print "Loaded evidence with {entries len
   - Expected: get_env_value(entries, "total_mismatched_pixels") equals `0`
   - Expected: get_env_value(entries, "total_pixels_compared") equals `1260`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "total_mismatched_pixels")).to_equal("0")
    expect(get_env_value(entries, "total_pixels_compared")).to_equal("1260")
```

</details>

#### full 88-char charset is byte-identical and advance is unified at 5*scale

- print "Loaded evidence with {entries len
   - Expected: get_env_value(entries, "strict_charset_count") equals `88`
   - Expected: get_env_value(entries, "strict_mismatched_chars") equals `0`
   - Expected: get_env_value(entries, "strict_mismatched_pixels") equals `0`
   - Expected: get_env_value(entries, "advance_engine2d") equals `10`
   - Expected: get_env_value(entries, "advance_browser") equals `10`
   - Expected: get_env_value(entries, "advance_match") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "strict_charset_count")).to_equal("88")
    expect(get_env_value(entries, "strict_mismatched_chars")).to_equal("0")
    expect(get_env_value(entries, "strict_mismatched_pixels")).to_equal("0")
    expect(get_env_value(entries, "advance_engine2d")).to_equal("10")
    expect(get_env_value(entries, "advance_browser")).to_equal("10")
    expect(get_env_value(entries, "advance_match")).to_equal("true")
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


## Related Documentation

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G2.5)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G2.5))


</details>
