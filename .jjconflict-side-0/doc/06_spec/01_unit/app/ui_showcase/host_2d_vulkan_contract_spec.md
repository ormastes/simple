# Vulkan-only 2D showcase host contract

> This is intentionally a source contract rather than a device test.  CI does

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan-only 2D showcase host contract

This is intentionally a source contract rather than a device test.  CI does

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | GPU DrawIR showcase capture provenance |
| Source | `test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This is intentionally a source contract rather than a device test.  CI does
not always expose a Vulkan device, but the optional showcase entry must still
fail closed: it may not turn an unavailable GPU, a CPU fallback, a partial
DrawIR lowering, or an unproven font render into a successful capture.

## Scenarios

### Vulkan 2D showcase host fail-closed contract

#### opens only an explicitly selected Vulkan Engine2D backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens only an explicitly selected Vulkan Engine2D backend
- Read the Vulkan-only adapter source


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("opens only an explicitly selected Vulkan Engine2D backend")
step("Read the Vulkan-only adapter source")
val source = vulkan_host_source()

expect(source.contains("Engine2D.create_with_backend_fast(w, h, \"vulkan\")") and
    source.contains("if engine.backend_name() != \"vulkan\":") and
    source.contains("engine.shutdown()") and source.contains("return nil")).to_equal(true)
```

</details>

#### requires GPU DrawIR and rejects CPU fallback, incomplete lowering, and weak readback provenance

- requires GPU DrawIR and rejects CPU fallback, incomplete lowering, and weak readback provenance
- Inspect the complete fresh-device receipt predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires GPU DrawIR and rejects CPU fallback, incomplete lowering, and weak readback provenance")
step("Inspect the complete fresh-device receipt predicate")
val source = vulkan_host_source()

expect(source.contains("composition.backend_target != DRAW_IR_BACKEND_GPU") and
    source.contains("engine2d_draw_ir_adv_strict_vulkan_primitives_with_images") and
    source.contains("result.selected_backend != \"gpu\"") and
    source.contains("result.fallback_required") and
    source.contains("result.fallback_reason != \"\"") and
    source.contains("result.skipped_command_count != 0") and
    source.contains("result.rendered_command_count <= 0") and
    source.contains("result.readback_source != \"device_readback\"") and
    source.contains("result.backend_handle <= 0") and
    source.contains("result.device_identity <= 0") and
    source.contains("result.readback_checksum <= 0") and
    source.contains("result.pixels.len() != expected_pixels") and
    source.contains("fresh-device-drawir-receipt-rejected")).to_equal(true)
```

</details>

#### requires a shared Vulkan font receipt with exact checksum and atlas evidence

- requires a shared Vulkan font receipt with exact checksum and atlas evidence
- Inspect the font-specific rejection predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires a shared Vulkan font receipt with exact checksum and atlas evidence")
step("Inspect the font-specific rejection predicate")
val source = vulkan_host_source()

expect(source.contains("result.font_execution_target != \"vulkan\"") and
    source.contains("result.font_identity == \"\"") and
    source.contains("result.font_batch_identity == \"\"") and
    source.contains("result.font_readback_source != \"device_readback\"") and
    source.contains("result.font_device_checksum != result.font_oracle_checksum") and
    source.contains("result.font_readback_nonblank_pixels <= 0") and
    source.contains("not result.font_parity") and
    source.contains("not result.font_device_executed") and
    source.contains("not result.font_promotion_ready") and
    source.contains("result.font_atlas_upload_count <= 0") and
    source.contains("result.font_atlas_upload_bytes <= 0") and
    source.contains("_lower_hex_sha256_valid(result.font_atlas_payload_sha256)") and
    source.contains("fresh-device-font-receipt-rejected")).to_equal(true)
```

</details>

#### does not accept lossy V3 presentation or claim a capture before a device result

- does not accept lossy V3 presentation or claim a capture before a device result
- Ensure composition presentation is the only successful render path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not accept lossy V3 presentation or claim a capture before a device result")
step("Ensure composition presentation is the only successful render path")
val source = vulkan_host_source()

expect(source.contains("vulkan-host-requires-original-composition") and
    source.contains("me present_scene(_scene: DrawIrV3Scene) -> bool:") and
    source.contains("me present_composition(composition: DrawIrComposition) -> bool:") and
    source.contains("self._accept_fresh_device_result(composition)") and
    source.contains("self.last_pixels = result.pixels") and
    source.contains("self.last_receipt =")).to_equal(true)
```

</details>

### Vulkan 2D showcase entry fail-closed contract

#### reports unavailable Vulkan as blocked and keeps GPU DrawIR explicit

- reports unavailable Vulkan as blocked and keeps GPU DrawIR explicit
- Read the explicit Vulkan entry source


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports unavailable Vulkan as blocked and keeps GPU DrawIR explicit")
step("Read the explicit Vulkan entry source")
val source = vulkan_entry_source()

expect(source.contains("DRAW_IR_BACKEND_GPU") and
    source.contains("Screen2dVulkanHost.open(w, h, script)") and
    source.contains("showcase status=blocked renderer=vulkan reason=vulkan-device-unavailable") and
    source.contains("showcase_run_with_backend(") and
    source.contains("DRAW_IR_BACKEND_GPU")).to_equal(true)
```

</details>

#### writes captures only from returned device pixels and emits the receipt

- writes captures only from returned device pixels and emits the receipt
- Inspect capture data flow and failure handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("writes captures only from returned device pixels and emits the receipt")
step("Inspect capture data flow and failure handling")
val source = vulkan_entry_source()

expect(source.contains("report.frames != frames") and
    source.contains("pixels.len() != w.to_i64() * h.to_i64()") and
    source.contains("receipt == \"\"") and
    source.contains("reason = \"incomplete-device-frame-sequence\"") and
    source.contains("reason={reason}") and
    source.contains("val pixels = host.pixels()") and
    source.contains("file_write_bytes(capture, raster_to_ppm_bytes(pixels, w, h))") and
    source.contains("reason=capture-write") and
    source.contains("{receipt}")) .to_equal(true)
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

- **Requirements:** `GPU DrawIR showcase capture provenance`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e538ee9a76d5f0e2739e5dabce5bf0025451696a682d09f18ab6ba536c1f2650`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e538ee9a76d5f0e2739e5dabce5bf0025451696a682d09f18ab6ba536c1f2650`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e538ee9a76d5f0e2739e5dabce5bf0025451696a682d09f18ab6ba536c1f2650`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl
mirror: doc/06_spec/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens only an explicitly selected Vulkan Engine2D backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires GPU DrawIR and rejects CPU fallback, incomplete lowering, and weak readback provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a shared Vulkan font receipt with exact checksum and atlas evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
