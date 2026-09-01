# Cross-App Glyph Consistency (Browser vs GUI Showcase)

> Verifies gate G2.5: "the browser and the GUI showcase render shared UI chrome ... with identical glyph rasterization and theme tokens (cross-app pixel oracle over shared widgets)."

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cross-app glyph consistency check produced evidence
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cross-app glyph consistency check produced evidence")
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

- cross-app glyph consistency check produced evidence
- capture+compare infrastructure ran successfully
   - Expected: get_env_value(entries, "driver_status") equals `pass`
   - Expected: get_env_value(entries, "overall") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cross-app glyph consistency check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("capture+compare infrastructure ran successfully")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "driver_status")).to_equal("pass")
    expect(get_env_value(entries, "overall")).to_equal("pass")
```

</details>

#### anchor glyphs 'A' and 'Z' render byte-identical ink in both apps

- cross-app glyph consistency check produced evidence
- anchor glyphs 'A' and 'Z' render byte-identical ink in both apps
   - Expected: get_env_value(entries, "char_0_glyph") equals `A`
   - Expected: get_env_value(entries, "char_0_status") equals `match`
   - Expected: get_env_value(entries, "char_0_mismatch_px") equals `0`
   - Expected: get_env_value(entries, "char_8_glyph") equals `Z`
   - Expected: get_env_value(entries, "char_8_status") equals `match`
   - Expected: get_env_value(entries, "char_8_mismatch_px") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cross-app glyph consistency check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("anchor glyphs 'A' and 'Z' render byte-identical ink in both apps")
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

- cross-app glyph consistency check produced evidence
- G2.5 closed: both paths rasterize byte-identically (no divergence)
   - Expected: get_env_value(entries, "glyph_consistency_status") equals `identical`
   - Expected: get_env_value(entries, "diverging_chars") equals `0`
   - Expected: get_env_value(entries, "char_1_glyph") equals `E`
   - Expected: get_env_value(entries, "char_1_status") equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cross-app glyph consistency check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("G2.5 closed: both paths rasterize byte-identically (no divergence)")
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

- cross-app glyph consistency check produced evidence
- rendered per-char oracle has zero mismatched pixels
   - Expected: get_env_value(entries, "total_mismatched_pixels") equals `0`
   - Expected: get_env_value(entries, "total_pixels_compared") equals `1260`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cross-app glyph consistency check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("rendered per-char oracle has zero mismatched pixels")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "total_mismatched_pixels")).to_equal("0")
    expect(get_env_value(entries, "total_pixels_compared")).to_equal("1260")
```

</details>

#### full 88-char charset is byte-identical and advance is unified at 5*scale

- cross-app glyph consistency check produced evidence
- full 88-char charset is byte-identical and advance is unified at 5*scale
   - Expected: get_env_value(entries, "strict_charset_count") equals `88`
   - Expected: get_env_value(entries, "strict_mismatched_chars") equals `0`
   - Expected: get_env_value(entries, "strict_mismatched_pixels") equals `0`
   - Expected: get_env_value(entries, "advance_engine2d") equals `10`
   - Expected: get_env_value(entries, "advance_browser") equals `10`
   - Expected: get_env_value(entries, "advance_match") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cross-app glyph consistency check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-cross-app-glyph-consistency.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("full 88-char charset is byte-identical and advance is unified at 5*scale")
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

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G2.5)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08c869bc4766d0dd5573410e520b1fe77049d7800cd5463ad9082954d0e9899a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08c869bc4766d0dd5573410e520b1fe77049d7800cd5463ad9082954d0e9899a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08c869bc4766d0dd5573410e520b1fe77049d7800cd5463ad9082954d0e9899a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/cross_app_glyph_consistency_spec.spl
mirror: doc/06_spec/03_system/check/cross_app_glyph_consistency_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/cross_app_glyph_consistency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/cross_app_glyph_consistency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/cross_app_glyph_consistency_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cross-app glyph consistency check produced evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/cross_app_glyph_consistency_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'capture+compare infrastructure ran successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/cross_app_glyph_consistency_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'anchor glyphs 'A' and 'Z' render byte-identical ink in both apps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
