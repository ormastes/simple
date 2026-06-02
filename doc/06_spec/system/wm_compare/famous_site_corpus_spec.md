# Famous Site Corpus Specification

## Scenarios

### famous-site renderer compatibility corpus

#### offline sample manifest

#### contains more than 100 deterministic site-inspired pages

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(samples.len()).to_be_greater_than(100)
```

</details>

#### uses complete HTML documents with stable ids

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(samples[0].id).to_start_with("site_0_")
expect(samples[0].html).to_start_with("<html>")
expect(samples[0].html).to_contain("</html>")
expect(samples[0].html).to_contain("Deterministic compatibility fixture")
expect(samples[0].html).to_contain("data-font-corpus=\"known-site-fonts\"")
expect(samples[0].html).to_contain("font-family: " + samples[0].font_family)
```

</details>

<details>
<summary>Advanced: covers a deterministic common-site font stack matrix</summary>

#### covers a deterministic common-site font stack matrix

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fonts = famous_site_font_families()
val samples = build_famous_site_sample_corpus()
expect(fonts.len()).to_be_greater_than(20)
expect(samples[0].font_family).to_equal(fonts[0])
expect(samples[fonts.len()].font_family).to_equal(fonts[0])
expect(samples[fonts.len() - 1].html).to_contain("font-family: " + fonts[fonts.len() - 1])
```

</details>


</details>

#### uses unique ids for every sample

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_has_duplicate_ids(samples)).to_equal(false)
```

</details>

#### covers the expected page categories

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_has_category(samples, "search")).to_equal(true)
expect(_has_category(samples, "video")).to_equal(true)
expect(_has_category(samples, "social")).to_equal(true)
expect(_has_category(samples, "commerce")).to_equal(true)
expect(_has_category(samples, "news")).to_equal(true)
expect(_has_category(samples, "productivity")).to_equal(true)
expect(_has_category(samples, "finance")).to_equal(true)
expect(_has_category(samples, "travel")).to_equal(true)
expect(_has_category(samples, "education")).to_equal(true)
expect(_has_category(samples, "developer")).to_equal(true)
expect(_has_category(samples, "cloud")).to_equal(true)
expect(_has_category(samples, "media")).to_equal(true)
```

</details>

#### exports a stable SDN manifest for future Chrome oracle jobs

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
val manifest = build_famous_site_sample_manifest_sdn()
expect(manifest).to_start_with("(famous_site_sample_corpus")
expect(manifest).to_contain("count: " + samples.len().to_string())
expect(manifest).to_contain("id: \"" + samples[0].id + "\"")
expect(manifest).to_contain("id: \"" + samples[samples.len() - 1].id + "\"")
expect(manifest).to_contain("font_family: \"" + samples[0].font_family + "\"")
expect(manifest).to_contain("html_path: \"" + famous_site_sample_html_path(samples[0].id) + "\"")
expect(manifest).to_contain("baseline_dir: \"" + famous_site_sample_baseline_dir(samples[0].id) + "\"")
expect(manifest).to_contain("chrome_ppm: \"" + famous_site_sample_chrome_ppm_path(samples[0].id) + "\"")
expect(manifest).to_contain("chrome_metrics: \"" + famous_site_sample_chrome_metrics_path(samples[0].id) + "\"")
expect(manifest).to_contain("simple_ppm: \"" + famous_site_sample_simple_ppm_path(samples[0].id) + "\"")
expect(manifest).to_contain("report_sdn: \"" + famous_site_sample_report_sdn_path(samples[0].id) + "\"")
```

</details>

#### uses deterministic future artifact paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(famous_site_sample_html_path(samples[0].id)).to_start_with("test/fixtures/famous_site_corpus/")
expect(famous_site_sample_html_path(samples[0].id)).to_end_with(".html")
expect(famous_site_sample_baseline_dir(samples[0].id)).to_start_with("test/baselines/famous_site_corpus/")
expect(famous_site_sample_chrome_ppm_path(samples[0].id)).to_end_with("/chrome.ppm")
expect(famous_site_sample_chrome_metrics_path(samples[0].id)).to_end_with("/chrome_metrics.json")
expect(famous_site_sample_simple_ppm_path(samples[0].id)).to_end_with("/simple.ppm")
expect(famous_site_sample_report_sdn_path(samples[0].id)).to_end_with("/report.sdn")
expect(famous_site_sample_production_simple_ppm_path(samples[0].id)).to_end_with("/simple.production.ppm")
expect(famous_site_sample_production_report_sdn_path(samples[0].id)).to_end_with("/report.production.sdn")
```

</details>

#### has every exported HTML fixture and manifest on disk

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(rt_file_exists("test/fixtures/famous_site_corpus/manifest.sdn")).to_equal(true)
expect(_all_fixture_files_exist(samples)).to_equal(true)
expect(_all_fixture_html_matches(samples)).to_equal(true)
expect(rt_file_read_text("test/fixtures/famous_site_corpus/manifest.sdn")).to_equal(build_famous_site_sample_manifest_sdn())
```

</details>

#### has every Chrome baseline, Simple capture, and comparison report on disk

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_all_baseline_artifacts_exist(samples)).to_equal(true)
```

</details>

#### has valid Chrome DOM metrics for every oracle sample

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_all_chrome_metrics_valid(samples)).to_equal(true)
```

</details>

#### has focused Chrome DOM metrics for the first failing oracle sample

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics_path = famous_site_sample_chrome_metrics_path("site_0_google")
expect(rt_file_exists(metrics_path)).to_equal(true)
val metrics = rt_file_read_text(metrics_path)
expect(metrics).to_contain("\"fontFamily\": \"\\\"Times New Roman\\\"\"")
expect(metrics).to_contain("\"marginTop\": \"8px\"")
expect(metrics).to_contain("\"textClientRects\"")
expect(metrics).to_contain("\"width\": 91.96875")
expect(metrics).to_contain("\"textLines\"")
expect(metrics).to_contain("\"text\": \"Google search\"")
expect(metrics).to_contain("\"text\": \"deterministic\"")
expect(metrics).to_contain("\"text\": \"compatibility\"")
expect(metrics).to_contain("\"text\": \"fixture\"")
expect(metrics).to_contain("\"canvasTextMetrics\"")
expect(metrics).to_contain("\"actualBoundingBoxAscent\": 12")
expect(metrics).to_contain("\"fontBoundingBoxAscent\": 14")
```

</details>

#### renders the first corpus page through the bounded child worker

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_process_run_timeout("bin/simple", [
    "run",
    "src/app/wm_compare/simple_html_capture_worker.spl",
    "--html=test/fixtures/famous_site_corpus/site_0_google.html",
    "--out=/tmp/famous_site_worker_google.ppm",
    "--width=160",
    "--height=120"
], 20000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("wrote /tmp/famous_site_worker_google.ppm pixels=19200")
expect(rt_file_exists("/tmp/famous_site_worker_google.ppm")).to_equal(true)
```

</details>

#### has a PPM delta diagnostic tool for the first failing oracle sample

<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/analyze_ppm_delta.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [
    tool_path,
    "test/baselines/famous_site_corpus/site_0_google/chrome.ppm",
    "test/baselines/famous_site_corpus/site_0_google/simple.ppm",
    "test/baselines/famous_site_corpus/site_0_google/chrome_metrics.json"
], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"differentPixels\": 0")
expect(result.0).to_contain("\"diffBox\"")
expect(result.0).to_contain("\"minX\": null")
expect(result.0).to_contain("\"maxY\": null")
expect(result.0).to_contain("\"sumAbsoluteChannelDiff\": 0")
expect(result.0).to_contain("\"channelAbsoluteDiff\"")
expect(result.0).to_contain("\"r\": 0")
expect(result.0).to_contain("\"g\": 0")
expect(result.0).to_contain("\"b\": 0")
expect(result.0).to_contain("\"channelSignedDiff\"")
expect(result.0).to_contain("\"b\": 0")
expect(result.0).to_contain("\"famousSiteRegions\"")
expect(result.0).to_contain("\"divBox\"")
expect(result.0).to_contain("\"differentPixels\": 0")
expect(result.0).to_contain("\"overflowText\"")
expect(result.0).to_contain("\"differentPixels\": 0")
expect(result.0).to_contain("\"belowOverflow\"")
expect(result.0).to_contain("\"textLines\"")
expect(result.0).to_contain("\"line1\"")
expect(result.0).to_contain("\"differentPixels\": 0")
expect(result.0).to_contain("\"textLineSegments\"")
expect(result.0).to_contain("\"line3Overflow\"")
expect(result.0).to_contain("\"sumAbsoluteChannelDiff\": 0")
```

</details>

#### has PPM delta diagnostics for the focused production renderer miss

<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/analyze_ppm_delta.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [
    tool_path,
    "test/baselines/famous_site_corpus/site_0_google/chrome.ppm",
    "test/baselines/famous_site_corpus/site_0_google/simple.production.ppm",
    "test/baselines/famous_site_corpus/site_0_google/chrome_metrics.json"
], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"differentPixels\": 2717")
expect(result.0).to_contain("\"sumAbsoluteChannelDiff\": 646916")
expect(result.0).to_contain("\"maxX\": 111")
expect(result.0).to_contain("\"maxY\": 75")
expect(result.0).to_contain("\"channelAbsoluteDiff\"")
expect(result.0).to_contain("\"b\": 295809")
expect(result.0).to_contain("\"famousSiteRegions\"")
expect(result.0).to_contain("\"divBox\"")
expect(result.0).to_contain("\"differentPixels\": 1612")
expect(result.0).to_contain("\"b\": 169893")
expect(result.0).to_contain("\"overflowText\"")
expect(result.0).to_contain("\"differentPixels\": 1104")
expect(result.0).to_contain("\"b\": 125876")
expect(result.0).to_contain("\"belowOverflow\"")
expect(result.0).to_contain("\"differentPixels\": 0")
expect(result.0).to_contain("\"line1\"")
expect(result.0).to_contain("\"differentPixels\": 808")
expect(result.0).to_contain("\"textLineSegments\"")
expect(result.0).to_contain("\"line3Overflow\"")
```

</details>

#### summarizes all corpus comparison reports for target selection

<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
val expected_stale = _stale_report_count(samples, 10000)
val tool_path = "tools/electron-shell/summarize_famous_site_corpus_reports.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--limit=3"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"reportCount\": 132")
expect(result.0).to_contain("\"exact\": 132")
expect(result.0).to_contain("\"accepted\": 132")
expect(result.0).to_contain("\"divergent\": 0")
expect(result.0).to_contain("\"staleSuspectThreshold\": 10000")
expect(result.0).to_contain("\"staleSuspectCount\": " + expected_stale.to_string())
expect(expected_stale).to_equal(0)
expect(result.0).to_contain("\"staleSuspects\": []")
expect(result.0).to_contain("\"staleReportCount\": 0")
expect(result.0).to_contain("\"staleReports\": []")
expect(result.0).to_contain("\"worst\"")
expect(result.0).to_contain("\"sample\": \"site_0_google\"")
expect(result.0).to_contain("\"differentPixels\": 0")
expect(result.0).to_contain("\"computedDifferentPixels\": 0")
expect(result.0).to_contain("\"reportFresh\": true")
expect(result.0).to_contain("\"best\"")
expect(result.0).to_contain("\"sample\": \"site_0_google\"")
expect(result.0).to_contain("\"differentPixels\": 0")
expect(result.0).to_contain("\"categorySummary\"")
```

</details>

#### passes the corpus completion gate when every report is exact

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/verify_famous_site_corpus_completion.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"status\": \"PASS\"")
expect(result.0).to_contain("\"reportCount\": 132")
expect(result.0).to_contain("\"exact\": 132")
expect(result.0).to_contain("\"accepted\": 132")
expect(result.0).to_contain("\"divergent\": 0")
expect(result.0).to_contain("\"staleReportCount\": 0")
expect(result.0).to_contain("\"checkedPixelReportCount\": 132")
expect(result.0).to_contain("\"computedMismatchCount\": 0")
expect(result.0).to_contain("\"failures\": []")
```

</details>

#### keeps fixture completion artifacts separate from production probe artifacts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_report_contains_exact_fixture_acceptance("site_0_google")).to_equal(true)
expect(_report_contains_bounded_production_miss("site_0_google")).to_equal(true)
```

</details>

#### fails the production probe gate when no generated production report exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/verify_famous_site_production_probe.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--sample=site_missing_never"], 10000)
expect(result.2).to_equal(1)
expect(result.0).to_contain("\"status\": \"FAIL\"")
expect(result.0).to_contain("\"sample\": \"site_missing_never\"")
expect(result.0).to_contain("missing production report")
```

</details>

#### fails the production probe gate without exact-pixel acceptance flags

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/verify_famous_site_production_probe.js"
expect(rt_file_exists(tool_path)).to_equal(true)
expect(rt_file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--sample=site_0_google", "--drop-acceptance-policy-flags-for-test"], 10000)
expect(result.2).to_equal(1)
expect(result.0).to_contain("\"status\": \"FAIL\"")
expect(result.0).to_contain("\"hasExactAcceptancePolicyFlags\": false")
expect(result.0).to_contain("missing structured exact-pixel acceptance policy flags")
```

</details>

#### fails the production probe gate when per-line ink text drifts from layout

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/verify_famous_site_production_probe.js"
expect(rt_file_exists(tool_path)).to_equal(true)
expect(rt_file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--sample=site_0_google", "--corrupt-text-line-ink-for-test"], 10000)
expect(result.2).to_equal(1)
expect(result.0).to_contain("\"status\": \"FAIL\"")
expect(result.0).to_contain("\"textMatchesLayout\": false")
expect(result.0).to_contain("per-line text ink entries do not match Simple layout line text")
```

</details>

#### fails the production probe gate when per-line ink no longer covers divergence

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/verify_famous_site_production_probe.js"
expect(rt_file_exists(tool_path)).to_equal(true)
expect(rt_file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--sample=site_0_google", "--drop-text-line-ink-difference-for-test"], 10000)
expect(result.2).to_equal(1)
expect(result.0).to_contain("\"status\": \"FAIL\"")
expect(result.0).to_contain("\"differentPixelsTotal\": 1908")
expect(result.0).to_contain("\"unexplainedDifferentPixels\": 809")
expect(result.0).to_contain("per-line text ink diagnostics do not account for production divergence")
```

</details>

#### passes the production probe gate for the focused production artifact

<details>
<summary>Executable SPipe</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/verify_famous_site_production_probe.js"
expect(rt_file_exists(tool_path)).to_equal(true)
expect(rt_file_exists(famous_site_sample_production_simple_ppm_path("site_0_google"))).to_equal(true)
expect(rt_file_exists(famous_site_sample_production_report_sdn_path("site_0_google"))).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--sample=site_0_google"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"status\": \"PASS\"")
expect(result.0).to_contain("\"rendererMode\": \"production\"")
expect(result.0).to_contain("\"divergent\": true")
expect(result.0).to_contain("\"maxDifferentPixels\": 2717")
expect(result.0).to_contain("\"differentPixels\": 2717")
expect(result.0).to_contain("\"computedDifferentPixels\": 2717")
expect(result.0).to_contain("\"reportFresh\": true")
expect(result.0).to_contain("\"hasSimpleLayoutLines\": true")
expect(result.0).to_contain("\"hasSimpleLayoutLineWidths\": true")
expect(result.0).to_contain("\"simpleLayoutLineCount\": 4")
expect(result.0).to_contain("\"hasTextGeometryDelta\": true")
expect(result.0).to_contain("\"chromeTextLineCount\": 4")
expect(result.0).to_contain("\"chromeCanvasMetricCount\": 4")
expect(result.0).to_contain("\"simpleGeometryLineCount\": 4")
expect(result.0).to_contain("\"textLineCountDelta\": 0")
expect(result.0).to_contain("\"layoutTextMatch\": true")
expect(result.0).to_contain("\"hasTextLineInkDelta\": true")
expect(result.0).to_contain("\"textLineInkDeltaCount\": 4")
expect(result.0).to_contain("\"detailCount\": 4")
expect(result.0).to_contain("\"differentPixelsTotal\": 2716")
expect(result.0).to_contain("\"unexplainedDifferentPixels\": 1")
expect(result.0).to_contain("\"textMatchesLayout\": true")
expect(result.0).to_contain("\"widthMatchesLayout\": true")
expect(result.0).to_contain("\"regionNamesSequential\": true")
expect(result.0).to_contain("\"textRegionDelta\"")
expect(result.0).to_contain("\"divBox\"")
expect(result.0).to_contain("\"differentPixels\": 1612")
expect(result.0).to_contain("\"overflowText\"")
expect(result.0).to_contain("\"differentPixels\": 1104")
expect(result.0).to_contain("\"b\": 169893")
```

</details>

#### summarizes corpus text coverage deficits for compositing targets

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/summarize_famous_site_corpus_coverage.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--limit=5"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"reportCount\": 132")
expect(result.0).to_contain("\"analyzedCount\": 132")
expect(result.0).to_contain("\"productionArtifactCount\": 1")
expect(result.0).to_contain("\"worstOverflow\"")
expect(result.0).to_contain("\"sample\": \"site_0_google\"")
expect(result.0).to_contain("\"artifact\": \"simple.production.ppm\"")
expect(result.0).to_contain("\"expectedPixels\": 1104")
expect(result.0).to_contain("\"actualPixels\": 0")
expect(result.0).to_contain("\"missingPixels\": 1104")
expect(result.0).to_contain("\"actualPct10000\": 0")
expect(result.0).to_contain("\"worstDivInk\"")
expect(result.0).to_contain("\"expectedBackground\": \"37,99,235\"")
expect(result.0).to_contain("\"expectedPixels\": 1612")
expect(result.0).to_contain("\"missingPixels\": 1612")
expect(result.0).to_contain("\"worstDiv\"")
expect(result.0).to_contain("\"differentPixels\": 1612")
```

</details>

#### summarizes colored-background text compositing deficits

<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/summarize_famous_site_text_compositing.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--limit=5"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"reportCount\": 132")
expect(result.0).to_contain("\"productionArtifactCount\": 1")
expect(result.0).to_contain("\"worstByInk\"")
expect(result.0).to_contain("\"sample\": \"site_0_google\"")
expect(result.0).to_contain("\"artifact\": \"simple.production.ppm\"")
expect(result.0).to_contain("\"expectedBackground\": \"37,99,235\"")
expect(result.0).to_contain("\"expectedInk\": 1612")
expect(result.0).to_contain("\"actualInk\": 0")
expect(result.0).to_contain("\"missingInk\": 1612")
expect(result.0).to_contain("\"actualPct10000\": 0")
expect(result.0).to_contain("\"expectedChromaticInk\": 1567")
expect(result.0).to_contain("\"channelSignedDiff\"")
expect(result.0).to_contain("\"r\": -27287")
expect(result.0).to_contain("\"b\": -169893")
expect(result.0).to_contain("\"channelAbsoluteDiff\"")
expect(result.0).to_contain("\"b\": 169893")
expect(result.0).to_contain("\"worstByDiff\"")
expect(result.0).to_contain("\"differentPixels\": 1612")
expect(result.0).to_contain("\"sad\": 269117")
```

</details>

#### summarizes colored-background text mask overlap deficits

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/summarize_famous_site_text_mask_overlap.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--limit=5"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"reportCount\": 132")
expect(result.0).to_contain("\"productionArtifactCount\": 1")
expect(result.0).to_contain("\"worstByRecall\"")
expect(result.0).to_contain("\"sample\": \"site_0_google\"")
expect(result.0).to_contain("\"artifact\": \"simple.production.ppm\"")
expect(result.0).to_contain("\"expectedBackground\": \"37,99,235\"")
expect(result.0).to_contain("\"expectedInk\": 1612")
expect(result.0).to_contain("\"actualInk\": 0")
expect(result.0).to_contain("\"overlapInk\": 0")
expect(result.0).to_contain("\"falsePositiveInk\": 0")
expect(result.0).to_contain("\"missingInk\": 1612")
expect(result.0).to_contain("\"precisionPct10000\": 0")
expect(result.0).to_contain("\"recallPct10000\": 0")
expect(result.0).to_contain("\"worstByFalsePositive\"")
expect(result.0).to_contain("\"falsePositiveInk\": 0")
```

</details>

#### summarizes colored-background text ink color histograms

<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/summarize_famous_site_text_color_histogram.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--limit=3", "--top=5"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"reportCount\": 3")
expect(result.0).to_contain("\"analyzedCount\": 3")
expect(result.0).to_contain("\"sample\": \"site_0_google\"")
expect(result.0).to_contain("\"artifact\": \"simple.production.ppm\"")
expect(result.0).to_contain("\"expectedBackground\": \"37,99,235\"")
expect(result.0).to_contain("\"expectedInk\"")
expect(result.0).to_contain("\"actualInk\": 0")
expect(result.0).to_contain("\"missingInk\"")
expect(result.0).to_contain("\"actualPct10000\": 0")
expect(result.0).to_contain("\"expectedUniqueInkColors\"")
expect(result.0).to_contain("\"actualUniqueInkColors\": 0")
expect(result.0).to_contain("\"expectedColors\"")
expect(result.0).to_contain("\"actualColors\": []")
expect(result.0).to_contain("\"sample\": \"site_15_twitch\"")
expect(result.0).to_contain("\"artifact\": \"simple.ppm\"")
expect(result.0).to_contain("\"actualPct10000\": 10000")
expect(result.0).to_contain("\"sample\": \"site_44_the_new_york_times\"")
```

</details>

#### calibrates corpus ink candidates for renderer tuning

<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/calibrate_famous_site_corpus_ink.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--limit=3"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"samples\"")
expect(result.0).to_contain("\"site_0_google\"")
expect(result.0).to_contain("\"site_44_the_new_york_times\"")
expect(result.0).to_contain("\"site_60_tripadvisor\"")
expect(result.0).to_contain("\"artifacts\"")
expect(result.0).to_contain("\"site_0_google\": \"simple.production.ppm\"")
expect(result.0).to_contain("\"base\"")
expect(result.0).to_contain("\"differentPixels\": 2717")
expect(result.0).to_contain("\"sad\": 646916")
expect(result.0).to_contain("\"expectedInk\": 4084")
expect(result.0).to_contain("\"actualInk\": 2472")
expect(result.0).to_contain("\"actualPct10000\": 6052")
expect(result.0).to_contain("\"bestByExact\"")
expect(result.0).to_contain("\"alpha\": 255")
expect(result.0).to_contain("\"bestBySad\"")
expect(result.0).to_contain("\"alpha\": 96")
expect(result.0).to_contain("\"sad\": 570024")
expect(result.0).to_contain("\"bestByInk\"")
expect(result.0).to_contain("\"candidates\"")
```

</details>

#### sweeps renderer-positioned text postprocess candidates

<details>
<summary>Executable SPipe</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_path = "tools/electron-shell/sweep_famous_site_text_postprocess.js"
expect(rt_file_exists(tool_path)).to_equal(true)
val result = rt_process_run_timeout("node", [tool_path, "--limit=3"], 10000)
expect(result.2).to_equal(0)
expect(result.0).to_contain("\"samples\"")
expect(result.0).to_contain("\"site_0_google\"")
expect(result.0).to_contain("\"site_15_twitch\"")
expect(result.0).to_contain("\"site_102_docker_hub\"")
expect(result.0).to_contain("\"artifacts\"")
expect(result.0).to_contain("\"site_0_google\": \"simple.production.ppm\"")
expect(result.0).to_contain("\"base\"")
expect(result.0).to_contain("\"differentPixels\": 2717")
expect(result.0).to_contain("\"sad\": 646916")
expect(result.0).to_contain("\"textPixels\": 1879")
expect(result.0).to_contain("\"bestByExact\"")
expect(result.0).to_contain("\"factor\": 1")
expect(result.0).to_contain("\"bestBySad\"")
expect(result.0).to_contain("\"bestByRgbExact\"")
expect(result.0).to_contain("\"rFactor\": 1")
expect(result.0).to_contain("\"gFactor\": 1")
expect(result.0).to_contain("\"bFactor\": 1")
expect(result.0).to_contain("\"bestByRgbSad\"")
expect(result.0).to_contain("\"bestByExpansionExact\"")
expect(result.0).to_contain("\"alpha\": 16")
expect(result.0).to_contain("\"differentPixels\": 3632")
expect(result.0).to_contain("\"bestByExpansionSad\"")
expect(result.0).to_contain("\"sad\": 669701")
expect(result.0).to_contain("\"bestByShiftExact\"")
expect(result.0).to_contain("\"dx\": 0")
expect(result.0).to_contain("\"dy\": 0")
expect(result.0).to_contain("\"bestByShiftSad\"")
expect(result.0).to_contain("\"bestByScopedShiftExact\"")
expect(result.0).to_contain("\"scope\": \"div\"")
expect(result.0).to_contain("\"bestByScopedShiftSad\"")
expect(result.0).to_contain("\"factorCandidates\"")
expect(result.0).to_contain("\"expansionCandidates\"")
```

</details>

#### reports mixed-font corpus wrapped-line mismatches with Simple line widths

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report_app = "src/app/wm_compare/site_corpus_layout_report.spl"
expect(rt_file_exists(report_app)).to_equal(true)
val report = build_site_corpus_layout_report(parse_site_corpus_layout_opts(["--limit=4"]))
expect(report).to_contain("(famous_site_corpus_layout_report")
expect(report).to_contain("selected: 4")
expect(report).to_contain("layout_width: 122")
expect(report).to_contain("first_mismatch: \"site_0_google\"")
expect(report).to_contain("missing_simple_line: \"compatibility fixture\"")
expect(report).to_contain("first_mismatch_widths:")
expect(report).to_contain("structural_layout_report")
expect(report).to_contain("source_a: \"chrome_metrics\"")
expect(report).to_contain("source_b: \"simple_layout\"")
```

</details>

#### documents the 120px mixed-font corpus wrapped-line boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report_app = "src/app/wm_compare/site_corpus_layout_report.spl"
expect(rt_file_exists(report_app)).to_equal(true)
val report = build_site_corpus_layout_report(parse_site_corpus_layout_opts(["--limit=4", "--layout-width=120"]))
expect(report).to_contain("selected: 4")
expect(report).to_contain("mismatched: 0")
expect(report).to_contain("layout_width: 120")
expect(report).to_contain("first_mismatch: \"\"")
```

</details>

#### documents the 132px mixed-font corpus wrapped-line over-merge boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report_app = "src/app/wm_compare/site_corpus_layout_report.spl"
expect(rt_file_exists(report_app)).to_equal(true)
val report = build_site_corpus_layout_report(parse_site_corpus_layout_opts(["--limit=4", "--layout-width=132"]))
expect(report).to_contain("selected: 4")
expect(report).to_contain("layout_width: 132")
expect(report).to_contain("first_mismatch: \"site_0_google\"")
expect(report).to_contain("missing_simple_line: \"compatibility fixture\"")
```

</details>

#### Simple Web Renderer smoke coverage

#### renders every corpus page to non-empty pixels

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_all_samples_render_non_empty(samples)).to_equal(true)
```

</details>

#### keeps the normal system font corpus capture pixel-aligned with Chrome

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val pixels = simple_web_render_html_to_pixels_with_corpus_fixtures(sample.html, 160, 120)
val chrome = _load_p6_ppm_pixels(famous_site_sample_chrome_ppm_path(sample.id), 160, 120)
expect(chrome.len()).to_equal(160 * 120)
expect(_pixels_equal(pixels, chrome)).to_equal(true)
```

</details>

#### keeps production renderer corpus compatibility distinct from fixture-oracle compatibility

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val production_pixels = simple_web_render_html_to_pixels(sample.html, 160, 120)
val fixture_pixels = simple_web_render_html_to_pixels_with_corpus_fixtures(sample.html, 160, 120)
val chrome = _load_p6_ppm_pixels(famous_site_sample_chrome_ppm_path(sample.id), 160, 120)
val exact = compare_exact(chrome, production_pixels, 160, 120)
val perceptual = compare_perceptual(chrome, production_pixels, 160, 120, 16, true)
expect(chrome.len()).to_equal(160 * 120)
expect(production_pixels.len()).to_equal(160 * 120)
expect(_pixels_equal(fixture_pixels, chrome)).to_equal(true)
expect(_pixels_equal(production_pixels, chrome)).to_equal(false)
expect(exact.different_pixels).to_be_greater_than(1000)
expect(exact.different_pixels).to_be_less_than(6000)
expect(exact.match_percentage).to_be_less_than(9900)
expect(perceptual.match_percentage).to_be_less_than(9900)
```

</details>

#### exposes Simple wrapped text lines for Chrome TextMetrics comparison

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val lines = br_famous_site_corpus_layout_lines_sdn(sample.html, 16, 120)
expect(lines).to_contain("count: 4")
expect(lines).to_contain("text: \"Google search\"")
expect(lines).to_contain("text: \"deterministic\"")
expect(lines).to_contain("text: \"compatibility\"")
expect(lines).to_contain("text: \"fixture\"")
```

</details>

#### documents the first over-wide mixed-font wrapped-line boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_first_simple_layout_line_missing_from_chrome_metrics(samples, 122)).to_equal("site_2_facebook: missing line compatibility fixture")
```

</details>

#### exposes Simple wrapped line widths for the calibrated mixed-font boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[28]
expect(sample.id).to_equal("site_28_google_translate")
val widths = br_famous_site_corpus_layout_line_widths_sdn(sample.html, 16, 120)
expect(widths).to_contain("text: \"Google\"")
expect(widths).to_contain("text: \"Translate news\"")
expect(widths).to_contain("text: \"deterministic\"")
expect(widths).to_contain("width:")
expect(widths).to_contain("count: 5")
```

</details>

#### keeps Engine2D software backend deterministic for corpus pages

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val default_pixels = simple_web_render_html_to_pixels(sample.html, 160, 120)
val engine_renderer = SimpleWebRenderer.create_with_backend(160, 120, "software")
val engine_pixels = engine_renderer.render_html_to_pixels(sample.html)
expect(engine_renderer.backend_name).to_equal("software")
expect(engine_pixels.len()).to_equal(160 * 120)
expect(_pixels_equal(default_pixels, engine_pixels)).to_equal(true)
```

</details>

#### Chrome oracle runner options

#### defaults to the corpus screenshot viewport

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_site_corpus_compat_opts([])
expect(opts.width).to_equal(160)
expect(opts.height).to_equal(120)
expect(opts.limit).to_equal(0)
expect(opts.from_id).to_equal("")
expect(opts.simple_timeout_ms).to_equal(60000)
expect(opts.update_baseline).to_equal(false)
expect(opts.skip_simple_watchdog).to_equal(false)
expect(opts.production_renderer).to_equal(false)
```

</details>

#### parses bounded corpus comparison options

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_site_corpus_compat_opts([
    "--only=site_0_google",
    "--from=site_28_google_translate",
    "--limit=1",
    "--width=200",
    "--height=150",
    "--simple-timeout-ms=3210",
    "--update-baseline",
    "--skip-simple",
    "--skip-simple-watchdog",
    "--production-renderer",
    "--stale-only",
    "--continue-on-fail"
])
expect(opts.only).to_equal("site_0_google")
expect(opts.from_id).to_equal("site_28_google_translate")
expect(opts.limit).to_equal(1)
expect(opts.width).to_equal(200)
expect(opts.height).to_equal(150)
expect(opts.simple_timeout_ms).to_equal(3210)
expect(opts.update_baseline).to_equal(true)
expect(opts.skip_simple).to_equal(true)
expect(opts.skip_simple_watchdog).to_equal(true)
expect(opts.production_renderer).to_equal(true)
expect(opts.stale_only).to_equal(true)
expect(opts.continue_on_fail).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/system/wm_compare/famous_site_corpus_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- famous-site renderer compatibility corpus

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

