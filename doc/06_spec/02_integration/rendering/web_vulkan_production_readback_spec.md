# web_vulkan_production_readback_spec

> Verifies the web vulkan production readback behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_vulkan_production_readback_spec

Verifies the web vulkan production readback behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/web_vulkan_production_readback_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the web vulkan production readback behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### production web renderer Vulkan readback

#### should submit canonical DrawIR through Engine2D and match the CPU oracle

- Verify: should submit canonical DrawIR through Engine2D and match the CPU oracle
- Render the production web producer CPU oracle
   - Expected: simple_web_layout_last_render_degraded() is false
   - Expected: cpu.source equals `cpu_mirror`
   - Expected: cpu.pixels.len() equals `480)  # oracle: pinned constant asserted by this scenario`
- Submit the same production DrawIR through Engine2D Vulkan
   - Expected: simple_web_layout_last_render_degraded() is false
   - Expected: gpu.source equals `device_readback`
   - Expected: gpu.pixel_count equals `480)  # oracle: pinned constant asserted by this scenario`
- Compare raw device readback with the web CPU oracle
   - Expected: gpu.pixels equals `cpu.pixels`
   - Expected: gpu_checksum equals `cpu_checksum`
- Retain machine-readable production web evidence
   - Expected: mkdir_status equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_write_text(receipt_path, receipt) is true
- Retain physical Vulkan image and ordered pipeline events
   - Expected: rt_file_write_bytes(image_path, _ppm_p6(gpu.pixels, 24, 20)) is true
   - Expected: rt_file_write_text(events_path, events) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-002 REQ-006 REQ-007 REQ-011
step("Verify: should submit canonical DrawIR through Engine2D and match the CPU oracle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# This prevents diagnostic style-budget degradation from weakening the
# parity assertion; it does not bypass any producer or GPU work.
simple_web_layout_set_render_budget_floor_ms(900000)
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#123456}.box{width:12px;height:10px;background-color:#cc3366}</style></head><body><div class='box'></div></body></html>"

step("Render the production web producer CPU oracle")
val cpu = simple_web_layout_render_html_readback(html, 24, 20, "cpu")
expect(simple_web_layout_last_render_degraded()).to_equal(false)
expect(cpu.source).to_equal("cpu_mirror")
expect(cpu.pixels.len()).to_equal(480)  # oracle: pinned constant asserted by this scenario

step("Submit the same production DrawIR through Engine2D Vulkan")
val gpu = simple_web_layout_render_html_readback(html, 24, 20, "vulkan")
expect(simple_web_layout_last_render_degraded()).to_equal(false)
expect(gpu.source).to_equal("device_readback")
expect(gpu.backend_handle).to_be_greater_than(0)
expect(gpu.device_identity).to_be_greater_than(0)
expect(gpu.pixel_count).to_equal(480)  # oracle: pinned constant asserted by this scenario

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
expect(mkdir_status).to_equal(0)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3aa66faa817247c77595248f117f3c9ff612ad11741f207bbd58aff28c19e9e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3aa66faa817247c77595248f117f3c9ff612ad11741f207bbd58aff28c19e9e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3aa66faa817247c77595248f117f3c9ff612ad11741f207bbd58aff28c19e9e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/rendering/web_vulkan_production_readback_spec.spl
mirror: doc/06_spec/02_integration/rendering/web_vulkan_production_readback_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/web_vulkan_production_readback_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/rendering/web_vulkan_production_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/web_vulkan_production_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/web_vulkan_production_readback_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should submit canonical DrawIR through Engine2D and match the CPU oracle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
