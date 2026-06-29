# HTML/CSS rendering manifest traceability gate

> Validates the lightweight gate that ties the WHATWG HTML element inventory and the implemented Simple Web CSS subset to actual rendered Electron/Simple layout fixtures. This is stronger than text-only SSpec assignment: the gate parses the 50-case layout capture manifest and the fixture HTML emitted by `check-electron-simple-web-layout-bitmap-evidence.shs`.

<!-- sdn-diagram:id=html_css_rendering_manifest_traceability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_css_rendering_manifest_traceability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_css_rendering_manifest_traceability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_css_rendering_manifest_traceability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML/CSS rendering manifest traceability gate

Validates the lightweight gate that ties the WHATWG HTML element inventory and the implemented Simple Web CSS subset to actual rendered Electron/Simple layout fixtures. This is stronger than text-only SSpec assignment: the gate parses the 50-case layout capture manifest and the fixture HTML emitted by `check-electron-simple-web-layout-bitmap-evidence.shs`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/html_css_rendering_manifest_traceability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the lightweight gate that ties the WHATWG HTML element inventory and
the implemented Simple Web CSS subset to actual rendered Electron/Simple layout
fixtures. This is stronger than text-only SSpec assignment: the gate parses the
50-case layout capture manifest and the fixture HTML emitted by
`check-electron-simple-web-layout-bitmap-evidence.shs`.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-html-css-rendering-manifest-traceability \
REPORT_PATH=build/test-html-css-rendering-manifest-traceability/report.md \
HTML_CSS_RENDERING_MANIFEST_FETCH=0 \
sh scripts/check/check-html-css-rendering-manifest-traceability.shs
```

## Acceptance

- The gate writes stable `html_css_rendering_manifest_traceability_*` evidence
  keys.
- All 105 current HTML elements have concrete rendered fixture element
  coverage; manifest prose alone is not sufficient.
- All implemented Simple Web CSS properties appear in actual rendered
  fixture CSS.
- The implemented CSS property list is loaded from the canonical SSpec
  traceability source, so the rendered-fixture gate cannot drift from the
  assignment inventory.
- Every scene in the 50-case manifest has a fixture HTML assignment.
- The manifest must keep the required 50-case render matrix, not just enough
  cases to cover the currently known tag/property names.

## Scenarios

### HTML/CSS rendering manifest traceability gate

<details>
<summary>Advanced: proves the rendered fixture matrix covers HTML tags and implemented CSS</summary>

#### proves the rendered fixture matrix covers HTML tags and implemented CSS

- Run the rendering manifest traceability check without network dependence
   - Expected: code equals `0`
- Read the emitted evidence contract
   - Expected: tag_count equals `105`
   - Expected: tag_covered equals `105`
   - Expected: tag_covered_names.split(",").len() equals `105`
   - Expected: tag_fixture_covered equals `105`
   - Expected: tag_manifest_only_count equals `0`
   - Expected: tag_manifest_only equals ``
   - Expected: tag_missing equals ``
   - Expected: css_count equals `248`
   - Expected: css_covered equals `248`
   - Expected: css_covered_names.split(",").len() equals `248`
   - Expected: css_missing equals ``
   - Expected: manifest_cases equals `50`
   - Expected: required_manifest_cases equals `50`
   - Expected: missing_fixture equals ``
- Verify the operator report was written


<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the rendering manifest traceability check without network dependence")
val command = "rm -rf build/test-html-css-rendering-manifest-traceability && BUILD_DIR=build/test-html-css-rendering-manifest-traceability REPORT_PATH=build/test-html-css-rendering-manifest-traceability/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 sh scripts/check/check-html-css-rendering-manifest-traceability.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the emitted evidence contract")
val evidence = file_read("build/test-html-css-rendering-manifest-traceability/evidence.env") ?? ""
expect(evidence).to_contain("html_css_rendering_manifest_traceability_status=pass")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_reason=pass")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_manifest=tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_fixture=scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_source=scripts/check/check-html-css-sspec-traceability.shs")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_source_status=pass")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_source_count=248")

val tag_count = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_count")
val tag_covered = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_covered_count")
val tag_covered_names = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_covered")
val tag_fixture_covered = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_fixture_covered_count")
val tag_manifest_only_count = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_manifest_only_count")
val tag_manifest_only = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_manifest_only")
val tag_missing = _value_of(evidence, "html_css_rendering_manifest_traceability_html_tag_missing")
val css_count = _value_of(evidence, "html_css_rendering_manifest_traceability_css_property_count")
val css_covered = _value_of(evidence, "html_css_rendering_manifest_traceability_css_property_covered_count")
val css_covered_names = _value_of(evidence, "html_css_rendering_manifest_traceability_css_property_covered")
val css_missing = _value_of(evidence, "html_css_rendering_manifest_traceability_css_property_missing")
val manifest_cases = _value_of(evidence, "html_css_rendering_manifest_traceability_manifest_case_count")
val required_manifest_cases = _value_of(evidence, "html_css_rendering_manifest_traceability_required_manifest_case_count")
val missing_fixture = _value_of(evidence, "html_css_rendering_manifest_traceability_manifest_missing_fixture")

expect(tag_count).to_equal("105")
expect(tag_covered).to_equal("105")
expect(tag_covered_names).to_contain("article")
expect(tag_covered_names).to_contain("video")
expect(tag_covered_names.split(",").len()).to_equal(105)
expect(tag_fixture_covered).to_equal("105")
expect(tag_manifest_only_count).to_equal("0")
expect(tag_manifest_only).to_equal("")
expect(tag_missing).to_equal("")
expect(css_count).to_equal("248")
expect(css_covered).to_equal("248")
expect(css_covered_names).to_contain("accent-color")
expect(css_covered_names).to_contain("align-content")
expect(css_covered_names).to_contain("align-items")
expect(css_covered_names).to_contain("align-self")
expect(css_covered_names).to_contain("clip")
expect(css_covered_names).to_contain("color-scheme")
expect(css_covered_names).to_contain("color-adjust")
expect(css_covered_names).to_contain("forced-color-adjust")
expect(css_covered_names).to_contain("print-color-adjust")
expect(css_covered_names).to_contain("orphans")
expect(css_covered_names).to_contain("widows")
expect(css_covered_names).to_contain("display")
expect(css_covered_names).to_contain("empty-cells")
expect(css_covered_names).to_contain("filter")
expect(css_covered_names).to_contain("justify-content")
expect(css_covered_names).to_contain("place-content")
expect(css_covered_names).to_contain("place-items")
expect(css_covered_names).to_contain("place-self")
expect(css_covered_names).to_contain("rotate")
expect(css_covered_names).to_contain("scale")
expect(css_covered_names).to_contain("border-style")
expect(css_covered_names).to_contain("transition-property")
expect(css_covered_names).to_contain("will-change")
expect(css_covered_names).to_contain("translate")
expect(css_covered_names.split(",").len()).to_equal(248)
expect(css_missing).to_equal("")
expect(manifest_cases).to_equal("50")
expect(required_manifest_cases).to_equal("50")
expect(missing_fixture).to_equal("")

step("Verify the operator report was written")
val report = file_read("build/test-html-css-rendering-manifest-traceability/report.md") ?? ""
expect(report).to_contain("# HTML/CSS Rendering Manifest Traceability")
expect(report).to_contain("- HTML tags: 105/105")
expect(report).to_contain("- implemented CSS properties: 248/248")
```

</details>


</details>

#### rejects a truncated render manifest even when fixture HTML still exists

- Create a manifest missing one render case and run the gate against it
   - Expected: code equals `0`
- Assert the gate fails on case count instead of silently accepting partial coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a manifest missing one render case and run the gate against it")
val command = "rm -rf build/test-html-css-rendering-manifest-traceability-truncated && mkdir -p build/test-html-css-rendering-manifest-traceability-truncated/source && head -n 50 tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt > build/test-html-css-rendering-manifest-traceability-truncated/source/truncated_manifest.txt && BUILD_DIR=build/test-html-css-rendering-manifest-traceability-truncated/out REPORT_PATH=build/test-html-css-rendering-manifest-traceability-truncated/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 HTML_CSS_RENDERING_MANIFEST_PATH=build/test-html-css-rendering-manifest-traceability-truncated/source/truncated_manifest.txt sh scripts/check/check-html-css-rendering-manifest-traceability.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the gate fails on case count instead of silently accepting partial coverage")
val evidence = file_read("build/test-html-css-rendering-manifest-traceability-truncated/out/evidence.env") ?? ""
expect(evidence).to_contain("html_css_rendering_manifest_traceability_status=fail")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_reason=unexpected-manifest-case-count")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_manifest=build/test-html-css-rendering-manifest-traceability-truncated/source/truncated_manifest.txt")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_manifest_case_count=49")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_required_manifest_case_count=50")
```

</details>

#### rejects canonical implemented CSS properties missing from rendered fixtures

- Create a temporary implemented CSS source with one extra supported property
   - Expected: code equals `0`
- Assert the rendered fixture gate follows the canonical implemented CSS source


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a temporary implemented CSS source with one extra supported property")
val command = "rm -rf build/test-html-css-rendering-manifest-traceability-extra-css && mkdir -p build/test-html-css-rendering-manifest-traceability-extra-css/source && cp scripts/check/check-html-css-sspec-traceability.shs build/test-html-css-rendering-manifest-traceability-extra-css/source/traceability.shs && perl -0pi -e 's/\"z-index\",/\"z-index\",\\n    \"simple-renderdoc-test-extra-property\",/' build/test-html-css-rendering-manifest-traceability-extra-css/source/traceability.shs && BUILD_DIR=build/test-html-css-rendering-manifest-traceability-extra-css/out REPORT_PATH=build/test-html-css-rendering-manifest-traceability-extra-css/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 HTML_CSS_RENDERING_IMPLEMENTED_CSS_SOURCE=build/test-html-css-rendering-manifest-traceability-extra-css/source/traceability.shs sh scripts/check/check-html-css-rendering-manifest-traceability.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the rendered fixture gate follows the canonical implemented CSS source")
val evidence = file_read("build/test-html-css-rendering-manifest-traceability-extra-css/out/evidence.env") ?? ""
expect(evidence).to_contain("html_css_rendering_manifest_traceability_status=fail")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_reason=css-properties-missing-rendering-fixture")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_source=build/test-html-css-rendering-manifest-traceability-extra-css/source/traceability.shs")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_source_status=pass")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_source_count=132")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_count=132")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_css_property_missing=simple-renderdoc-test-extra-property")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md](doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md)


</details>
