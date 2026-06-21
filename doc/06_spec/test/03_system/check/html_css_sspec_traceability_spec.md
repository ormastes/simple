# HTML/CSS SSpec traceability gate

> Validates the typed evidence gate for WHATWG HTML element and W3C CSS property inventory assignment to the SSpec corpus. This is the text/spec inventory companion to the rendered fixture manifest traceability gate.

<!-- sdn-diagram:id=html_css_sspec_traceability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_css_sspec_traceability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_css_sspec_traceability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_css_sspec_traceability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML/CSS SSpec traceability gate

Validates the typed evidence gate for WHATWG HTML element and W3C CSS property inventory assignment to the SSpec corpus. This is the text/spec inventory companion to the rendered fixture manifest traceability gate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/html_css_sspec_traceability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the typed evidence gate for WHATWG HTML element and W3C CSS
property inventory assignment to the SSpec corpus. This is the text/spec
inventory companion to the rendered fixture manifest traceability gate.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-html-css-sspec-traceability \
REPORT_PATH=build/test-html-css-sspec-traceability/report.md \
sh scripts/check/check-html-css-sspec-traceability.shs
```

## Acceptance

- The gate writes stable `html_css_sspec_traceability_*` evidence keys.
- The current WHATWG HTML element inventory has 105 assigned elements.
- The current W3C CSS inventory has at least 390 property-like entries assigned.
- The implemented Simple Web CSS subset remains traceable to its generated
  combinations spec.
- CSS properties outside the implemented Simple Web subset are checked against
  concrete per-property tokens in the unsupported inventory SSpec.

## Scenarios

### HTML/CSS SSpec traceability gate

#### emits typed evidence for HTML and CSS SSpec inventory coverage

- Run the HTML/CSS SSpec traceability gate
   - Expected: code equals `0`
- Read the emitted typed evidence
   - Expected: html_count equals `105`
   - Expected: missing_html equals ``
   - Expected: missing_css_count equals `0`
   - Expected: unsupported_missing equals ``
- Verify the operator report was written


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the HTML/CSS SSpec traceability gate")
val command = "rm -rf build/test-html-css-sspec-traceability && BUILD_DIR=build/test-html-css-sspec-traceability REPORT_PATH=build/test-html-css-sspec-traceability/report.md sh scripts/check/check-html-css-sspec-traceability.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the emitted typed evidence")
val evidence = rt_file_read_text("build/test-html-css-sspec-traceability/evidence.env") ?? ""
expect(evidence).to_contain("html_css_sspec_traceability_status=pass")
expect(evidence).to_contain("html_css_sspec_traceability_reason=pass")
expect(evidence).to_contain("html_css_sspec_traceability_required_html_tag_count=105")
expect(evidence).to_contain("html_css_sspec_traceability_required_css_property_min_count=390")
expect(evidence).to_contain("html_css_sspec_traceability_css_property_missing_count=0")
expect(evidence).to_contain("html_css_sspec_traceability_implemented_css_property_count=62")
expect(evidence).to_contain("html_css_sspec_traceability_implemented_css_property_missing_count=0")
expect(evidence).to_contain("html_css_sspec_traceability_unsupported_css_property_missing_count=0")
expect(evidence).to_contain("html_css_sspec_traceability_implemented_css_subset_spec=test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl")
expect(evidence).to_contain("html_css_sspec_traceability_unsupported_css_inventory_spec=test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl")

val html_count = _value_of(evidence, "html_css_sspec_traceability_html_tag_count")
val css_count = _value_of(evidence, "html_css_sspec_traceability_css_property_count")
val missing_html = _value_of(evidence, "html_css_sspec_traceability_html_tag_missing")
val missing_css_count = _value_of(evidence, "html_css_sspec_traceability_css_property_missing_count")
val indexed_implemented_css_count = _value_of(evidence, "html_css_sspec_traceability_implemented_css_property_indexed_count")
val unsupported_css_count = _value_of(evidence, "html_css_sspec_traceability_unsupported_css_property_count")
val unsupported_missing = _value_of(evidence, "html_css_sspec_traceability_unsupported_css_property_missing")

expect(html_count).to_equal("105")
expect(css_count.to_i64()).to_be_greater_than(389)
expect(missing_html).to_equal("")
expect(missing_css_count).to_equal("0")
expect(indexed_implemented_css_count.to_i64()).to_be_greater_than(55)
expect(unsupported_css_count.to_i64()).to_be_greater_than(330)
expect(unsupported_missing).to_equal("")

step("Verify the operator report was written")
val report = rt_file_read_text("build/test-html-css-sspec-traceability/report.md") ?? ""
expect(report).to_contain("# HTML/CSS SSpec Traceability")
expect(report).to_contain("- WHATWG HTML elements: 105/105")
expect(report).to_contain("- W3C CSS property-like entries:")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md](doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md)


</details>
