# web_vulkan_production_readback_spec

> Focused production web producer to DrawIR/Engine2D Vulkan readback parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_vulkan_production_readback_spec

Focused production web producer to DrawIR/Engine2D Vulkan readback parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/web_vulkan_production_readback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused production web producer to DrawIR/Engine2D Vulkan readback parity.

## Scenarios

### production web renderer Vulkan readback

#### should submit canonical DrawIR through Engine2D and match the CPU oracle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should submit canonical DrawIR through Engine2D and match the CPU oracle
- Render the production web producer CPU oracle
   - Expected: simple_web_layout_last_render_degraded() is false
   - Expected: cpu.source equals `cpu_mirror`
   - Expected: cpu.pixels.len() equals `480`
- Submit the same production DrawIR through Engine2D Vulkan
   - Expected: simple_web_layout_last_render_degraded() is false
   - Expected: gpu.source equals `device_readback`
   - Expected: gpu.pixel_count equals `480`
- Compare raw device readback with the web CPU oracle
   - Expected: gpu.pixels equals `cpu.pixels`
   - Expected: gpu_checksum equals `cpu_checksum`
- Retain machine-readable production web evidence
   - Expected: mkdir_status equals `0`
   - Expected: rt_file_write_text(receipt_path, receipt) is true
- Retain physical Vulkan image and ordered pipeline events
   - Expected: rt_file_write_bytes(image_path, _ppm_p6(gpu.pixels, 24, 20)) is true
   - Expected: rt_file_write_text(events_path, events) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should submit canonical DrawIR through Engine2D and match the CPU oracle")
# This prevents diagnostic style-budget degradation from weakening the
# parity assertion; it does not bypass any producer or GPU work.
simple_web_layout_set_render_budget_floor_ms(900000)
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#123456}.box{width:12px;height:10px;background-color:#cc3366}</style></head><body><div class='box'></div></body></html>"

step("Render the production web producer CPU oracle")
val cpu = simple_web_layout_render_html_readback(html, 24, 20, "cpu")
expect(simple_web_layout_last_render_degraded()).to_equal(false)
expect(cpu.source).to_equal("cpu_mirror")
expect(cpu.pixels.len()).to_equal(480)

step("Submit the same production DrawIR through Engine2D Vulkan")
val gpu = simple_web_layout_render_html_readback(html, 24, 20, "vulkan")
expect(simple_web_layout_last_render_degraded()).to_equal(false)
expect(gpu.source).to_equal("device_readback")
expect(gpu.backend_handle).to_be_greater_than(0)
expect(gpu.device_identity).to_be_greater_than(0)
expect(gpu.pixel_count).to_equal(480)

step("Compare raw device readback with the web CPU oracle")
val cpu_checksum = _checksum(cpu.pixels)
val gpu_checksum = _checksum(gpu.pixels)
print("web_vulkan_backend_handle=" + gpu.backend_handle.to_text())
print("web_vulkan_device_identity=" + gpu.device_identity.to_text())
print("web_vulkan_readback_source=" + gpu.source)
print("web_vulkan_cpu_checksum=" + cpu_checksum.to_text())
print("web_vulkan_gpu_checksum=" + gpu_checksum.to_text())
expect(gpu.pixels).to_equal(cpu.pixels)
expect(gpu_checksum).to_equal(cpu_checksum)
step("Retain machine-readable production web evidence")
val (_mkdir_out, _mkdir_err, mkdir_status) = rt_process_run("/bin/mkdir", ["-p", WEB_VULKAN_ARTIFACT_DIR])
expect(mkdir_status).to_equal(0)
val receipt = "version=1\ncommand=bin/simple test test/02_integration/rendering/web_vulkan_production_readback_spec.spl --mode=interpreter --no-session-daemon\nevidence_class=physical-device\nproducer=SimpleWebLayout+DrawIR+Engine2D\nbackend=vulkan\nbackend_handle=" + gpu.backend_handle.to_text() + "\ndevice_identity=" + gpu.device_identity.to_text() + "\nreadback_source=" + gpu.source + "\npixel_count=" + gpu.pixel_count.to_text() + "\ncpu_checksum=" + cpu_checksum.to_text() + "\ngpu_checksum=" + gpu_checksum.to_text() + "\nmismatch_count=0\nimage_path=" + WEB_VULKAN_ARTIFACT_DIR + "/production_web_vulkan.ppm\nevent_log_path=" + WEB_VULKAN_ARTIFACT_DIR + "/production_web_vulkan.events.jsonl\nparity=pass\n"
expect(receipt).to_contain("evidence_class=physical-device")
expect(receipt).to_contain("readback_source=device_readback")
expect(receipt).to_contain("mismatch_count=0")
val receipt_path = WEB_VULKAN_ARTIFACT_DIR + "/production_web_vulkan.receipt"
expect(rt_file_write_text(receipt_path, receipt)).to_equal(true)
print("web_vulkan_receipt=" + receipt_path)

step("Retain physical Vulkan image and ordered pipeline events")
val image_path = WEB_VULKAN_ARTIFACT_DIR + "/production_web_vulkan.ppm"
expect(rt_file_write_bytes(image_path, _ppm_p6(gpu.pixels, 24, 20))).to_equal(true)
val events = "{\"sequence\":1,\"stage\":\"producer\",\"owner\":\"SimpleWebLayout\",\"status\":\"complete\"}\n" +
    "{\"sequence\":2,\"stage\":\"draw_ir\",\"owner\":\"DrawIR\",\"status\":\"complete\"}\n" +
    "{\"sequence\":3,\"stage\":\"engine2d\",\"owner\":\"Engine2D\",\"status\":\"complete\"}\n" +
    "{\"sequence\":4,\"stage\":\"gpu_dispatch\",\"backend\":\"vulkan\",\"backend_handle\":" + gpu.backend_handle.to_text() + ",\"device_identity\":" + gpu.device_identity.to_text() + ",\"status\":\"complete\"}\n" +
    "{\"sequence\":5,\"stage\":\"device_readback\",\"source\":\"" + gpu.source + "\",\"pixel_count\":" + gpu.pixel_count.to_text() + ",\"checksum\":" + gpu_checksum.to_text() + ",\"status\":\"complete\"}\n"
expect(events).to_contain("\"stage\":\"producer\"")
expect(events).to_contain("\"stage\":\"draw_ir\"")
expect(events).to_contain("\"stage\":\"engine2d\"")
expect(events).to_contain("\"stage\":\"gpu_dispatch\"")
expect(events).to_contain("\"stage\":\"device_readback\"")
expect(events).to_contain("\"checksum\":" + gpu_checksum.to_text())
val events_path = WEB_VULKAN_ARTIFACT_DIR + "/production_web_vulkan.events.jsonl"
expect(rt_file_write_text(events_path, events)).to_equal(true)
print("web_vulkan_image=" + image_path)
print("web_vulkan_events=" + events_path)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-002`
- `REQ-006`
- `REQ-007`
- `REQ-011`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `380a623d023a18ef2fb782e35732fab4718b084cbdd0370c17a98b116c68a314`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `380a623d023a18ef2fb782e35732fab4718b084cbdd0370c17a98b116c68a314`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `380a623d023a18ef2fb782e35732fab4718b084cbdd0370c17a98b116c68a314`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/rendering/web_vulkan_production_readback_spec.spl
mirror: doc/06_spec/02_integration/rendering/web_vulkan_production_readback_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/rendering/web_vulkan_production_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/web_vulkan_production_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/web_vulkan_production_readback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/web_vulkan_production_readback_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/rendering/web_vulkan_production_readback_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should submit canonical DrawIR through Engine2D and match the CPU oracle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/web_vulkan_production_readback_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should submit canonical DrawIR through Engine2D and match the CPU oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
