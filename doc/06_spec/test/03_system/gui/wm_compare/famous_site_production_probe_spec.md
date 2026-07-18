# Famous Site Production Probe Spec

> Focused production probe coverage for the current Chrome parity gate. This keeps

<!-- sdn-diagram:id=famous_site_production_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=famous_site_production_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

famous_site_production_probe_spec -> std
famous_site_production_probe_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=famous_site_production_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Famous Site Production Probe Spec

Focused production probe coverage for the current Chrome parity gate. This keeps

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/famous_site_production_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Focused production probe coverage for the current Chrome parity gate. This keeps
fast metadata and fail-closed checks out of the full 42-scenario corpus sweep.

The production renderer composites Chrome-calibrated LCD glyph ink
(calibrated atlas: test/09_baselines/famous_site_corpus/glyph_atlas/, generated
by tools/electron-shell/generate_famous_site_glyph_atlas.js). The remaining
bounded divergence is 3 pixels of overlapping-glyph fringe stacking inside the
blue div box.

## Scenarios

### famous-site production probe

#### passes the focused production artifact as bounded divergent evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_tool_path())).to_equal(true)
expect(file_exists(famous_site_sample_production_simple_ppm_path("site_0_google"))).to_equal(true)
expect(file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = process_run_timeout("node", [_tool_path(), "--sample=site_0_google"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"status\": \"PASS\"")
expect(result.0).to_contain("\"rendererMode\": \"production\"")
expect(result.0).to_contain("\"productionRenderStrategy\": \"famous_site_calibrated_lcd_glyph_compositing_v1\"")
expect(result.0).to_contain("\"parityStatus\": \"divergent\"")
expect(result.0).to_contain("\"boundedDivergenceOnly\": true")
expect(result.0).to_contain("\"chromeGlyphCompositingParity\": false")
expect(result.0).to_contain("\"promotionRequiredDifferentPixels\": 3")
expect(result.0).to_contain("\"differentPixels\": 3")
expect(result.0).to_contain("\"computedDifferentPixels\": 3")
expect(result.0).to_contain("\"allRegionCountsMatch\": true")
expect(result.0).to_contain("\"unexplainedDifferentPixels\": 0")
expect(result.0).to_contain("\"residualDifference\"")
expect(result.0).to_contain("\"count\": 0")
expect(result.0).to_contain("\"first\": null")
expect(result.0).to_contain("\"differentPixelsTotal\": 3")
expect(result.0).to_contain("\"reportFresh\": true")
```

</details>

#### fails closed when per-line ink position drifts from pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_tool_path())).to_equal(true)
expect(file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = process_run_timeout("node", [_tool_path(), "--sample=site_0_google", "--corrupt-text-line-ink-position-for-test"], 10000)
expect(result.2).to_equal(1)
expect(result.0).to_contain("\"status\": \"FAIL\"")
expect(result.0).to_contain("\"allRegionCountsMatch\": false")
expect(result.0).to_contain("\"reportedDifferentPixels\": 2")
expect(result.0).to_contain("\"actualDifferentPixels\": 1")
expect(result.0).to_contain("per-line text ink region geometry does not match production pixels")
```

</details>

#### fails closed when residual pixel diagnostics drift from unexplained divergence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(_tool_path())).to_equal(true)
expect(file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = process_run_timeout("node", [_tool_path(), "--sample=site_0_google", "--hide-residual-difference-for-test"], 10000)
expect(result.2).to_equal(1)
expect(result.0).to_contain("\"status\": \"FAIL\"")
expect(result.0).to_contain("\"unexplainedDifferentPixels\": 0")
expect(result.0).to_contain("\"count\": 1")
expect(result.0).to_contain("residual pixel diagnostics do not match unexplained production divergence")
```

</details>

#### summarizes the production text-compositing result for renderer tuning

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/summarize_famous_site_text_compositing.js"
expect(file_exists(tool_path)).to_equal(true)
expect(file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = process_run_timeout("node", [tool_path, "--limit=1"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"productionArtifactCount\": 1")
expect(result.0).to_contain("\"sample\": \"site_0_google\"")
expect(result.0).to_contain("\"artifact\": \"simple.production.ppm\"")
expect(result.0).to_contain("\"expectedBackground\": \"37,99,235\"")
expect(result.0).to_contain("\"expectedInk\": 1612")
expect(result.0).to_contain("\"actualInk\": 1612")
expect(result.0).to_contain("\"missingInk\": 0")
expect(result.0).to_contain("\"actualPct10000\": 10000")
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
