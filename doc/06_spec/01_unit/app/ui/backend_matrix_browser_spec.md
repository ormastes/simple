# Backend Matrix Browser Specification

> Tests covering GUI widget matrix browser backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Browser Specification

## Scenarios

### GUI widget matrix browser backend

#### renders through the shared web API without a document shell

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders through the shared web API without a document shell
   - Expected: e equals ``
   - Expected: e equals ``
   - Expected: html contains `widget-button`
   - Expected: html contains `widget-statusbar`
   - Expected: html does not contain `<html>`
   - Expected: backend.web_render_target equals `pure_simple`
   - Expected: backend.viewport_width() equals `64`
   - Expected: backend.viewport_height() equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders through the shared web API without a document shell")
val tree_result = parse_ui_to_tree("examples/06_io/ui/widget_matrix.ui.sdn")
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        val state = init_state(tree)
        val backend_result = BrowserBackend.create(64, 48, "software")
        match backend_result:
            Err(e):
                expect(e).to_equal("")
            Ok(backend):
                val html = backend.render_html(state)
                expect(html.contains("widget-button")).to_equal(true)
                expect(html.contains("widget-statusbar")).to_equal(true)
                expect(html.contains("<html>")).to_equal(false)
                expect(backend.web_render_target).to_equal("pure_simple")
                expect(backend.viewport_width()).to_equal(64)
                expect(backend.viewport_height()).to_equal(48)
```

</details>

#### keeps canonical Engine2D backend selection visible through the browser adapter

- keeps canonical Engine2D backend selection visible through the browser adapter
   - Expected: BrowserBackend.create(64, 48, "cuda").unwrap().gpu_backend() equals `cuda`
   - Expected: BrowserBackend.create(64, 48, "hip").unwrap().gpu_backend() equals `rocm`
   - Expected: BrowserBackend.create(64, 48, "opencl").unwrap().gpu_backend() equals `opencl`
   - Expected: BrowserBackend.create(64, 48, "vulkan").unwrap().gpu_backend() equals `vulkan`
   - Expected: BrowserBackend.create(64, 48, "simd_cpu").unwrap().gpu_backend() equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps canonical Engine2D backend selection visible through the browser adapter")
expect(BrowserBackend.create(64, 48, "cuda").unwrap().gpu_backend()).to_equal("cuda")
expect(BrowserBackend.create(64, 48, "hip").unwrap().gpu_backend()).to_equal("rocm")
expect(BrowserBackend.create(64, 48, "opencl").unwrap().gpu_backend()).to_equal("opencl")
expect(BrowserBackend.create(64, 48, "vulkan").unwrap().gpu_backend()).to_equal("vulkan")
expect(BrowserBackend.create(64, 48, "simd_cpu").unwrap().gpu_backend()).to_equal("cpu_simd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_matrix_browser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GUI widget matrix browser backend.
- GUI widget matrix browser backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89627232bbe16e931774cb00105bafa82324a7a3da1080137c4d07c4edc013a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89627232bbe16e931774cb00105bafa82324a7a3da1080137c4d07c4edc013a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89627232bbe16e931774cb00105bafa82324a7a3da1080137c4d07c4edc013a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/ui/backend_matrix_browser_spec.spl
mirror: doc/06_spec/01_unit/app/ui/backend_matrix_browser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/backend_matrix_browser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/backend_matrix_browser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/backend_matrix_browser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/backend_matrix_browser_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders through the shared web API without a document shell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/backend_matrix_browser_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps canonical Engine2D backend selection visible through the browser adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
