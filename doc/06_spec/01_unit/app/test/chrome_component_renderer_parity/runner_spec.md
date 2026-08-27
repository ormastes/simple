# runner_spec

> Purpose and audience: bounded-runner verification for the Chrome component

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# runner_spec

Purpose and audience: bounded-runner verification for the Chrome component

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/chrome_component_renderer_parity/runner_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: bounded-runner verification for the Chrome component
renderer parity harness. Scope: turning injected bounded Chrome process
outcomes into receipts, failing closed on broken captures, decoding
independent Simple adapter receipts, and rejecting absent records. Audience:
renderer parity maintainers.

requirements: doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md
architecture: doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md

## Scenarios

### Chrome component renderer parity bounded runner

#### turns an injected bounded process result and complete artifacts into a receipt

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Bounded capture validation (expected show, folded, detail, or skip)


- Plan a Chrome capture for the first manifest fixture
   - Text capture: after_step
- Validate an injected successful process outcome with complete artifacts
- Read the admitted production receipt
   - Expected: result.status equals `pass`
   - Expected: result.receipt.backend equals `chrome`
   - Expected: result.receipt.semantic_input_hash equals `input-sha`
   - Expected: result.receipt.production_path is true
   - Expected: result.receipt.pixel_artifact_hash equals `pixel-sha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-WEB-RENDERER-PARITY-RECEIPT
step("Plan a Chrome capture for the first manifest fixture")
val fixture = load_parity_manifest(DEFAULT_PARITY_MANIFEST).cases[0]
val root = "build/test-artifacts/injected-chrome"
val plan = chrome_capture_plan(fixture, "/opt/chrome", "chrome-pinned-sha", root)
step("Validate an injected successful process outcome with complete artifacts")
val result = validate_chrome_capture_result(plan, fixture, "input-sha",
    ParityProcessOutcome(stdout: "captured", stderr: "", exit_code: 0),
    injected_artifacts(root, fixture.id))
step("Read the admitted production receipt")
expect(result.status).to_equal("pass")
expect(result.receipt.backend).to_equal("chrome")
expect(result.receipt.semantic_input_hash).to_equal("input-sha")
expect(result.receipt.production_path).to_equal(true)
expect(result.receipt.pixel_artifact_hash).to_equal("pixel-sha")
```

</details>

#### fails closed on process failure blank pixels and invalid proof

- Plan a capture and inject a failed process with blank pixels and a failing proof
   - Text capture: after_step
- Verify the validation fails closed with multiple blockers and a stale receipt
   - Expected: result.status equals `fail`
   - Expected: result.receipt.fresh is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-WEB-RENDERER-PARITY-FAIL-CLOSED
step("Plan a capture and inject a failed process with blank pixels and a failing proof")
val fixture = load_parity_manifest(DEFAULT_PARITY_MANIFEST).cases[0]
val root = "build/test-artifacts/injected-chrome"
val plan = chrome_capture_plan(fixture, "/opt/chrome", "chrome-pinned-sha", root)
val result = validate_chrome_capture_result(plan, fixture, "input-sha",
    ParityProcessOutcome(stdout: "", stderr: "capture failed", exit_code: 2),
    injected_artifacts(root, fixture.id, proof: "{\"status\":\"fail\"}", pixels: 0))
step("Verify the validation fails closed with multiple blockers and a stale receipt")
expect(result.status).to_equal("fail")
# oracle: >2 blockers because process failure, zero pixel bytes, and invalid proof each raise one.
expect(result.blockers.len()).to_be_greater_than(2)
expect(result.receipt.fresh).to_equal(false)
```

</details>

#### decodes and admits already-produced independent Simple adapter receipts

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Simple adapter receipt decoding (expected show, folded, detail, or skip)


- Assemble three independent adapter receipt records
   - Text capture: after_step
- Verify all records decode and orchestrate with the chrome receipt
   - Expected: decoded.valid() is true
   - Expected: decoded.receipts.len() equals `3`
   - Expected: orchestrate_adapter_receipts(chrome, decoded.receipts).valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-WEB-RENDERER-PARITY-ADAPTER-RECEIPTS
step("Assemble three independent adapter receipt records")
val fixture_id = "fixture"
val input_hash = "input-sha"
val content = "(receipt fixture_id: \"fixture\" backend: \"simple_cpu\" run_id: \"run-cpu\" semantic_input_hash: \"input-sha\" stage_artifact_path: \"cpu/stage\" stage_artifact_hash: \"sc\" pixel_artifact_path: \"cpu/pixel\" pixel_artifact_hash: \"pc\" producer: \"cpu-adapter\" fresh: true production_path: true fallback: false)\n" +
    "(receipt fixture_id: \"fixture\" backend: \"simple_simd\" run_id: \"run-simd\" semantic_input_hash: \"input-sha\" stage_artifact_path: \"simd/stage\" stage_artifact_hash: \"ss\" pixel_artifact_path: \"simd/pixel\" pixel_artifact_hash: \"ps\" producer: \"simd-adapter\" fresh: true production_path: true fallback: false)\n" +
    "(receipt fixture_id: \"fixture\" backend: \"simple_gpu\" run_id: \"run-gpu\" semantic_input_hash: \"input-sha\" stage_artifact_path: \"gpu/stage\" stage_artifact_hash: \"sg\" pixel_artifact_path: \"gpu/pixel\" pixel_artifact_hash: \"pg\" producer: \"gpu-adapter\" fresh: true production_path: true fallback: false)"
val decoded = decode_simple_adapter_receipts(content)
step("Verify all records decode and orchestrate with the chrome receipt")
expect(decoded.valid()).to_equal(true)
# oracle: 3 = one decoded record per backend lane (cpu, simd, gpu) in the content.
expect(decoded.receipts.len()).to_equal(3)
val chrome = ParityExecutionReceipt(fixture_id: fixture_id, backend: "chrome", run_id: "run-chrome",
    semantic_input_hash: input_hash, stage_artifact_path: "chrome/stage", stage_artifact_hash: "schrome",
    pixel_artifact_path: "chrome/pixel", pixel_artifact_hash: "pchrome", producer: "chrome-capture",
    fresh: true, production_path: true, fallback: false)
expect(orchestrate_adapter_receipts(chrome, decoded.receipts).valid()).to_equal(true)
```

</details>

#### rejects absent adapter receipt records

- Decode an empty adapter receipt stream
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: decode_simple_adapter_receipts("").valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-WEB-RENDERER-PARITY-ADAPTER-RECEIPTS
step("Decode an empty adapter receipt stream")
expect(decode_simple_adapter_receipts("").valid()).to_equal(false)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GPU-WEB-RENDERER-PARITY-RECEIPT`
- `REQ-GPU-WEB-RENDERER-PARITY-FAIL-CLOSED`
- `REQ-GPU-WEB-RENDERER-PARITY-ADAPTER-RECEIPTS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f02d9698dec1abc1e13e80d0675526619093b5725ae2eedd7a64bba22dd8dcff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f02d9698dec1abc1e13e80d0675526619093b5725ae2eedd7a64bba22dd8dcff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f02d9698dec1abc1e13e80d0675526619093b5725ae2eedd7a64bba22dd8dcff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: 01_unit/app/test/chrome_component_renderer_parity/runner_spec.spl
mirror: doc/06_spec/chrome_component_renderer_parity/runner_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/chrome_component_renderer_parity/runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/chrome_component_renderer_parity/runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/chrome_component_renderer_parity/runner_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/chrome_component_renderer_parity/runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
