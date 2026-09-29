# production_rows_spec

> Purpose and audience: production-row verification for the Chrome component

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# production_rows_spec

Purpose and audience: production-row verification for the Chrome component

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/chrome_component_renderer_parity/production_rows_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: production-row verification for the Chrome component
renderer parity harness. Scope: one real fixture executed independently on the
CPU and SIMD backends, normalization of pinned public Chrome captures, and
rejection of forged or tampered artifacts. Audience: renderer parity maintainers.

requirements: doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md
architecture: doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md

## Scenarios

### Chrome component renderer parity production rows

#### observes one real fixture and executes CPU and SIMD independently

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Production row execution (expected show, folded, detail, or skip)


- Build a single focused fixture requiring both backends
   - Text capture: after_step
- Run the fixture row on cpu and cpu_simd lanes
- Read the receipts: both lanes pass with distinct run ids
   - Expected: result.status equals `pass`
   - Expected: result.receipts.len() equals `2`
   - Expected: result.receipts[0].backend equals `simple_cpu`
   - Expected: result.receipts[1].backend equals `simple_simd`
   - Expected: result.receipts[0].run_id == result.receipts[1].run_id is false
   - Expected: result.comparison_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-WEB-RENDERER-PARITY-ROWS
step("Build a single focused fixture requiring both backends")
val fixture = ParityFixtureCase(id: "focused-cpu-simd", corpus: "focused_generated",
    source_kind: "file", source_ref: "test/fixtures/chrome_component_renderer_parity/cases/blank_visible_sentinel.html",
    width: 17, height: 19, dpr_milli: 1000,
    source_sha256: "fixture-sha", config_hash: "config-sha", font_hash: "font-sha",
    locale: "en-US", timezone: "UTC", clock_ms: 0, interaction: "none",
    supported_features: ["html", "css"], required_backends: ["simple_cpu", "simple_simd"],
    policy_id: "exact", policy_version: 1, channel_delta: 0, max_differing_pixels: 0)
step("Run the fixture row on cpu and cpu_simd lanes")
val result = execute_simple_fixture_rows(fixture, file_read_text(fixture.source_ref),
    "test-revision", "build/test-artifacts/chrome_component_renderer_parity_unit",
    ["cpu", "cpu_simd"], 1000, 1048576, "unit-run-1")
step("Read the receipts: both lanes pass with distinct run ids")
expect(result.status).to_equal("pass")
# oracle: 2 receipts because the fixture requires one cpu and one simd backend.
expect(result.receipts.len()).to_equal(2)
expect(result.receipts[0].backend).to_equal("simple_cpu")
expect(result.receipts[1].backend).to_equal("simple_simd")
expect(result.receipts[0].run_id == result.receipts[1].run_id).to_equal(false)
# oracle: one comparison receipt per executed backend lane.
expect(result.comparison_count).to_equal(2)
```

</details>

#### normalizes pinned Chrome public geometry and ARGB pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Pinned Chrome capture normalization (expected show, folded, detail, or skip)


- Assemble a pinned Chrome headless proof, geometry, and ARGB capture
   - Text capture: after_step
- Normalize the capture into the parity row format
- Verify the decoded RGBA8 bytes and stage payload
   - Expected: output.backend equals `chrome`
   - Expected: output.rgba8 equals `[255u8, 0u8, 0u8, 255u8, 0u8, 255u8, 0u8, 255u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-WEB-RENDERER-PARITY-CHROME-NORMALIZE
step("Assemble a pinned Chrome headless proof, geometry, and ARGB capture")
val proof = "{\"status\":\"pass\",\"proof_source\":\"tools/chrome-live-bitmap/capture_html_argb.js\",\"width\":2,\"height\":1,\"chrome_bin\":\"/opt/chrome\",\"chrome_product\":\"Chrome/123\",\"chrome_protocol_version\":\"1.3\",\"chrome_user_agent\":\"HeadlessChrome/123\"}"
val geometry = "{\"producer\":\"chrome-headless-geometry\",\"viewport\":{\"width\":2,\"height\":1},\"items\":[{\"tag\":\"div\",\"label\":\"box\",\"x\":0,\"y\":0,\"width\":2,\"height\":1,\"display\":\"block\",\"fontSize\":\"16px\",\"lineHeight\":\"normal\"}]}"
# oracle: 4294901760 = 0xFFFF0000 ARGB (opaque red), 4278255360 = 0xFF00FF00 (opaque green) — pinned Chrome output pixels.
val pixels = "{\"producer\":\"chrome-headless-screenshot\",\"width\":2,\"height\":1,\"format\":\"argb-u32\",\"pixels\":[4294901760,4278255360]}"
step("Normalize the capture into the parity row format")
val normalized = normalize_chrome_capture("chrome-case", "<div>box</div>", 2, 1,
    "/opt/chrome", proof, "proof-sha", geometry, pixels, "pixel-sha", 1000, 1048576)
match normalized:
    Err(reason): fail("valid Chrome artifacts rejected: " + reason)
    Ok(output):
        step("Verify the decoded RGBA8 bytes and stage payload")
        expect(output.backend).to_equal("chrome")
        expect(output.rgba8).to_equal([255u8, 0u8, 0u8, 255u8, 0u8, 255u8, 0u8, 255u8])
        expect(output.stages[0].payload).to_contain("chrome-public-geometry-v1")
```

</details>

#### rejects forged identity and tampered pixel metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Forged artifact rejection (expected show, folded, detail, or skip)


- Assemble an unpinned proof plus a tampered pixel producer
   - Text capture: after_step
- Attempt normalization and require rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-WEB-RENDERER-PARITY-CHROME-AUTHENTICITY
step("Assemble an unpinned proof plus a tampered pixel producer")
val forged_proof = "{\"status\":\"pass\",\"proof_source\":\"tools/chrome-live-bitmap/capture_html_argb.js\",\"width\":1,\"height\":1,\"chrome_bin\":\"/other/chrome\",\"chrome_product\":\"Chrome/123\",\"chrome_protocol_version\":\"1.3\",\"chrome_user_agent\":\"HeadlessChrome/123\"}"
val geometry = "{\"producer\":\"chrome-headless-geometry\",\"viewport\":{\"width\":1,\"height\":1},\"items\":[{\"tag\":\"div\",\"label\":\"box\",\"x\":0,\"y\":0,\"width\":1,\"height\":1}]}"
val tampered = "{\"producer\":\"fixture-oracle\",\"width\":1,\"height\":1,\"format\":\"argb-u32\",\"pixels\":[4294967295]}"
step("Attempt normalization and require rejection")
val result = normalize_chrome_capture("forged", "<div></div>", 1, 1, "/opt/chrome",
    forged_proof, "proof-sha", geometry, tampered, "pixel-sha", 1, 1)
match result:
    Ok(_): fail("forged Chrome artifacts must not normalize")
    Err(reason): expect(reason).to_contain("unpinned")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GPU-WEB-RENDERER-PARITY-ROWS`
- `REQ-GPU-WEB-RENDERER-PARITY-CHROME-NORMALIZE`
- `REQ-GPU-WEB-RENDERER-PARITY-CHROME-AUTHENTICITY`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f290de81a178673d85ebc7ddab06ce01a93f7bb6878d39e34523a3d71d19829c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f290de81a178673d85ebc7ddab06ce01a93f7bb6878d39e34523a3d71d19829c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f290de81a178673d85ebc7ddab06ce01a93f7bb6878d39e34523a3d71d19829c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: 01_unit/app/test/chrome_component_renderer_parity/production_rows_spec.spl
mirror: doc/06_spec/chrome_component_renderer_parity/production_rows_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=85 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/chrome_component_renderer_parity/production_rows_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
test/chrome_component_renderer_parity/production_rows_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/chrome_component_renderer_parity/production_rows_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/chrome_component_renderer_parity/production_rows_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/chrome_component_renderer_parity/production_rows_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
