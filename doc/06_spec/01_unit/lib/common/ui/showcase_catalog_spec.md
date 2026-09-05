# Showcase Catalog Specification

> Tests covering showcase catalog.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Showcase Catalog Specification

## Scenarios

### showcase catalog

#### contains exactly three unique stable app IDs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- contains exactly three unique stable app IDs
   - Expected: entries.len() equals `3`
   - Expected: entries[0].app_id equals `GRAPHICS_2D_SHOWCASE_APP_ID`
   - Expected: entries[1].app_id equals `WEB_STANDARDS_SHOWCASE_APP_ID`
   - Expected: entries[2].app_id equals `GUI_WIDGET_SHOWCASE_APP_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains exactly three unique stable app IDs")
val entries = showcase_catalog()
expect(entries.len()).to_equal(3)
expect(entries[0].app_id).to_equal(GRAPHICS_2D_SHOWCASE_APP_ID)
expect(entries[1].app_id).to_equal(WEB_STANDARDS_SHOWCASE_APP_ID)
expect(entries[2].app_id).to_equal(GUI_WIDGET_SHOWCASE_APP_ID)
```

</details>

#### describes the graphics 2D showcase and its installed package

- describes the graphics 2D showcase and its installed package
   - Expected: entry.app_id equals `graphics_2d_showcase`
   - Expected: entry.title equals `2D Rendering Showcase`
   - Expected: entry.source_path equals `examples/06_io/ui/graphics_2d_showcase_gui.spl`
   - Expected: entry.page_path equals ``
   - Expected: entry.installed_path equals `/sys/apps/graphics_2d_showcase.smf`
   - Expected: showcase_installed_path(entry) equals `/sys/apps/graphics_2d_showcase.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("describes the graphics 2D showcase and its installed package")
val found = showcase_find(GRAPHICS_2D_SHOWCASE_APP_ID)
assert_not_equal(found, nil)
if val entry = found:
    expect(entry.app_id).to_equal("graphics_2d_showcase")
    expect(entry.title).to_equal("2D Rendering Showcase")
    expect(entry.source_path).to_equal("examples/06_io/ui/graphics_2d_showcase_gui.spl")
    expect(entry.page_path).to_equal("")
    expect(entry.installed_path).to_equal("/sys/apps/graphics_2d_showcase.smf")
    expect(showcase_installed_path(entry)).to_equal("/sys/apps/graphics_2d_showcase.smf")
```

</details>

#### describes the web standards showcase and its installed package

- describes the web standards showcase and its installed package
   - Expected: entry.app_id equals `web_standards_showcase`
   - Expected: entry.title equals `Web Standards Showcase`
   - Expected: entry.source_path equals `examples/06_io/ui/web_standards_showcase_gui.spl`
   - Expected: entry.page_path equals `examples/06_io/ui/browser_common_elements_showcase.html`
   - Expected: entry.installed_path equals `/sys/apps/web_standards_showcase.smf`
   - Expected: showcase_installed_path(entry) equals `/sys/apps/web_standards_showcase.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("describes the web standards showcase and its installed package")
val found = showcase_find(WEB_STANDARDS_SHOWCASE_APP_ID)
assert_not_equal(found, nil)
if val entry = found:
    expect(entry.app_id).to_equal("web_standards_showcase")
    expect(entry.title).to_equal("Web Standards Showcase")
    expect(entry.source_path).to_equal("examples/06_io/ui/web_standards_showcase_gui.spl")
    expect(entry.page_path).to_equal("examples/06_io/ui/browser_common_elements_showcase.html")
    expect(entry.installed_path).to_equal("/sys/apps/web_standards_showcase.smf")
    expect(showcase_installed_path(entry)).to_equal("/sys/apps/web_standards_showcase.smf")
```

</details>

#### describes the GUI widget showcase and its installed package

- describes the GUI widget showcase and its installed package
   - Expected: entry.app_id equals `gui_widget_showcase`
   - Expected: entry.title equals `Widget Showcase`
   - Expected: entry.source_path equals `examples/06_io/ui/widget_showcase_gui.spl`
   - Expected: entry.page_path equals ``
   - Expected: entry.installed_path equals `/sys/apps/gui_widget_showcase.smf`
   - Expected: showcase_installed_path(entry) equals `/sys/apps/gui_widget_showcase.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("describes the GUI widget showcase and its installed package")
val found = showcase_find(GUI_WIDGET_SHOWCASE_APP_ID)
assert_not_equal(found, nil)
if val entry = found:
    expect(entry.app_id).to_equal("gui_widget_showcase")
    expect(entry.title).to_equal("Widget Showcase")
    expect(entry.source_path).to_equal("examples/06_io/ui/widget_showcase_gui.spl")
    expect(entry.page_path).to_equal("")
    expect(entry.installed_path).to_equal("/sys/apps/gui_widget_showcase.smf")
    expect(showcase_installed_path(entry)).to_equal("/sys/apps/gui_widget_showcase.smf")
```

</details>

#### reports only currently implemented launch surfaces

- reports only currently implemented launch surfaces
   - Expected: showcase_surface_supported(graphics, ShowcaseSurface.Standalone) is false
   - Expected: showcase_surface_supported(web, ShowcaseSurface.Standalone) is false
   - Expected: showcase_surface_supported(widgets, ShowcaseSurface.Standalone) is false
   - Expected: showcase_surface_supported(graphics, ShowcaseSurface.HostWm) is false
   - Expected: showcase_surface_supported(web, ShowcaseSurface.HostWm) is false
   - Expected: showcase_surface_supported(widgets, ShowcaseSurface.HostWm) is false
   - Expected: showcase_surface_supported(graphics, ShowcaseSurface.SimpleOsWm) is false
   - Expected: showcase_surface_supported(web, ShowcaseSurface.SimpleOsWm) is false
   - Expected: showcase_surface_supported(widgets, ShowcaseSurface.SimpleOsWm) is false
   - Expected: showcase_surface_supported(graphics, ShowcaseSurface.SimpleOs2d) is false
   - Expected: showcase_surface_supported(web, ShowcaseSurface.SimpleOs2d) is false
   - Expected: showcase_surface_supported(widgets, ShowcaseSurface.SimpleOs2d) is false
   - Expected: showcase_surface_supported(graphics, ShowcaseSurface.SimpleOsWeb) is false
   - Expected: showcase_surface_supported(web, ShowcaseSurface.SimpleOsWeb) is false
   - Expected: showcase_surface_supported(widgets, ShowcaseSurface.SimpleOsWeb) is false
   - Expected: showcase_surface_supported(graphics, ShowcaseSurface.SimpleOsGui) is false
   - Expected: showcase_surface_supported(web, ShowcaseSurface.SimpleOsGui) is false
   - Expected: showcase_surface_supported(widgets, ShowcaseSurface.SimpleOsGui) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports only currently implemented launch surfaces")
val entries = showcase_catalog()
val graphics = entries[0]
val web = entries[1]
val widgets = entries[2]
expect(showcase_surface_supported(graphics, ShowcaseSurface.Standalone)).to_equal(false)
expect(showcase_surface_supported(web, ShowcaseSurface.Standalone)).to_equal(false)
expect(showcase_surface_supported(widgets, ShowcaseSurface.Standalone)).to_equal(false)
expect(showcase_surface_supported(graphics, ShowcaseSurface.HostWm)).to_equal(false)
expect(showcase_surface_supported(web, ShowcaseSurface.HostWm)).to_equal(false)
expect(showcase_surface_supported(widgets, ShowcaseSurface.HostWm)).to_equal(false)
expect(showcase_surface_supported(graphics, ShowcaseSurface.SimpleOsWm)).to_equal(false)
expect(showcase_surface_supported(web, ShowcaseSurface.SimpleOsWm)).to_equal(false)
expect(showcase_surface_supported(widgets, ShowcaseSurface.SimpleOsWm)).to_equal(false)
expect(showcase_surface_supported(graphics, ShowcaseSurface.SimpleOs2d)).to_equal(false)
expect(showcase_surface_supported(web, ShowcaseSurface.SimpleOs2d)).to_equal(false)
expect(showcase_surface_supported(widgets, ShowcaseSurface.SimpleOs2d)).to_equal(false)
expect(showcase_surface_supported(graphics, ShowcaseSurface.SimpleOsWeb)).to_equal(false)
expect(showcase_surface_supported(web, ShowcaseSurface.SimpleOsWeb)).to_equal(false)
expect(showcase_surface_supported(widgets, ShowcaseSurface.SimpleOsWeb)).to_equal(false)
expect(showcase_surface_supported(graphics, ShowcaseSurface.SimpleOsGui)).to_equal(false)
expect(showcase_surface_supported(web, ShowcaseSurface.SimpleOsGui)).to_equal(false)
expect(showcase_surface_supported(widgets, ShowcaseSurface.SimpleOsGui)).to_equal(false)
```

</details>

#### rejects unknown IDs and contains no empty metadata

- rejects unknown IDs and contains no empty metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unknown IDs and contains no empty metadata")
expect(showcase_find("unknown_showcase")).to_be_nil()
for entry in showcase_catalog():
    expect(entry.app_id.len()).to_be_greater_than(0)
    expect(entry.title.len()).to_be_greater_than(0)
    expect(entry.source_path.len()).to_be_greater_than(0)
    expect(entry.installed_path.len()).to_be_greater_than(0)
    if entry.app_id == WEB_STANDARDS_SHOWCASE_APP_ID:
        expect(entry.page_path.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/showcase_catalog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering showcase catalog.
- showcase catalog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `836863fb8bb89a372107cd88f0fb2c936a544cf1d1cb3b421dacb2ccc3124729`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `836863fb8bb89a372107cd88f0fb2c936a544cf1d1cb3b421dacb2ccc3124729`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `836863fb8bb89a372107cd88f0fb2c936a544cf1d1cb3b421dacb2ccc3124729`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/ui/showcase_catalog_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/showcase_catalog_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/showcase_catalog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/showcase_catalog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/showcase_catalog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/showcase_catalog_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains exactly three unique stable app IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/showcase_catalog_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'describes the graphics 2D showcase and its installed package' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/showcase_catalog_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'describes the web standards showcase and its installed package' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
