# vulkan_compiler_fill_rect_live_spec

> Verifies the vulkan compiler fill rect live behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_compiler_fill_rect_live_spec

Verifies the vulkan compiler fill rect live behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the vulkan compiler fill rect live behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### compiler-produced Vulkan FillRect

#### should pass spirv-val and return exact physical-device pixels

- Verify: should pass spirv-val and return exact physical-device pixels
- Lower representative drawing semantics through frontend HIR MIR and Vulkan
   - Expected: hir_lowering.errors.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: mir_lowering.errors.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: compiled.is_ok() is true
- Compile and validate the compiler-produced SPIR-V artifact
   - Expected: rt_file_write_text(assembly_path, assembly) is true
   - Expected: as_status equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: as_err equals ``
   - Expected: val_status equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: val_err equals ``
- Submit native work and capture device readback
   - Expected: session.init() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.device_type == "discrete" or session.device_type == "integrated" is true
   - Expected: vulkan_sffi_copy_to_buffer(output, zeroes, 0) is true
   - Expected: vulkan_dispatch_framebuffer_compute_checked(output, pipeline, _u32_le(6), 1, 1, 1) equals `1)  # oracle: pinned constant asserted by this scenario`
- Compare device readback with the CPU oracle
   - Expected: readback equals `expected`
- Retain compiler validator and physical readback provenance
   - Expected: mkdir_status equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_write_text(retained_assembly, assembly) is true
   - Expected: rt_file_write_bytes(retained_binary, spirv) is true
   - Expected: artifact_sha_status equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: artifact_sha_err equals ``
   - Expected: artifact_sha.len() equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_write_text(receipt_path, receipt) is true
   - Expected: vulkan_sffi_free_buffer(output) is true
   - Expected: vulkan_sffi_destroy_pipeline(pipeline) is true
   - Expected: vulkan_sffi_destroy_shader(shader) is true
   - Expected: vulkan_sffi_shutdown_reaped() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 98 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-002 REQ-006 REQ-007 REQ-011
step("Verify: should pass spirv-val and return exact physical-device pixels")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Lower representative drawing semantics through frontend HIR MIR and Vulkan")
val source = "@gpu(\"vulkan\")\n" +
    "fn processing_fill_rect_u32(mut output: [u32], n: u32) -> ():\n" +
    "    val i = gpu_global_id(0)\n" +
    "    if i < n:\n" +
    "        output[i + 50u32] = 0xff3366ccu32\n" +
    "        output[i + 66u32] = 0xff3366ccu32\n" +
    "        output[i + 82u32] = 0xff3366ccu32\n" +
    "        output[i + 98u32] = 0xff3366ccu32\n" +
    "        output[i + 114u32] = 0xff3366ccu32\n"
val parsed = parse_full_frontend(source, "processing_fill_rect_u32.spl", "processing_fill_rect_u32", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("processing_fill_rect_u32.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
var mir_lowering = MirLowering.new(hir.symbols)
val mir = mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
val compiled = vulkan_compile_module_direct(mir)
expect(compiled.is_ok()).to_equal(true)
val assembly = compiled.unwrap().text_output
expect(assembly).to_contain("OpStore")
expect(assembly).to_contain("Binding 0")

val assembly_path = "/tmp/simple_processing_fill_rect.spvasm"
val binary_path = "/tmp/simple_processing_fill_rect.spv"
step("Compile and validate the compiler-produced SPIR-V artifact")
expect(rt_file_write_text(assembly_path, assembly)).to_equal(true)
val (_as_out, as_err, as_status) = rt_process_run("spirv-as", ["--target-env", "vulkan1.3", assembly_path, "-o", binary_path])
expect(as_status).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(as_err).to_equal("")
val (_val_out, val_err, val_status) = rt_process_run("spirv-val", ["--target-env", "vulkan1.3", binary_path])
expect(val_status).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(val_err).to_equal("")
val spirv = rt_file_read_bytes(binary_path)
expect(spirv.len()).to_be_greater_than(20)

step("Submit native work and capture device readback")
var session = VulkanSession.create()
expect(session.init()).to_equal(0)  # oracle: pinned constant asserted by this scenario
print("processing_fill_rect_device_name=" + session.device_name)
print("processing_fill_rect_device_type=" + session.device_type)
print("processing_fill_rect_driver_identity=" + session.driver_identity)
expect(session.device_type == "discrete" or session.device_type == "integrated").to_equal(true)
expect(session.driver_identity.len()).to_be_greater_than(0)
val shader = vulkan_sffi_compile_spirv(spirv)
expect(shader).to_be_greater_than(0)
val pipeline = vulkan_sffi_create_compute_pipeline(shader, "processing_fill_rect_u32", 4)
expect(pipeline).to_be_greater_than(0)
val output = vulkan_sffi_alloc_buffer(1024, 0x80)
expect(output).to_be_greater_than(0)
val zeroes: [u8] = [0u8; 1024]
expect(vulkan_sffi_copy_to_buffer(output, zeroes, 0)).to_equal(true)
expect(vulkan_dispatch_framebuffer_compute_checked(output, pipeline, _u32_le(6), 1, 1, 1)).to_equal(1)  # oracle: pinned constant asserted by this scenario
val readback = vulkan_sffi_read_buffer_bytes(output, 1024, 0)
step("Compare device readback with the CPU oracle")
val expected = _expected_rect_bytes()
var mismatch_count: i64 = 0
var byte_index: i64 = 0
while byte_index < expected.len().to_i64():
    if readback[byte_index] != expected[byte_index]:
        mismatch_count = mismatch_count + 1
    byte_index = byte_index + 1
print("processing_fill_rect_readback_bytes=" + readback.len().to_text())
print("processing_fill_rect_mismatch_count=" + mismatch_count.to_text())
expect(readback).to_equal(expected)

step("Retain compiler validator and physical readback provenance")
val (_mkdir_out, _mkdir_err, mkdir_status) = rt_process_run("/bin/mkdir", ["-p", VULKAN_COMPILER_ARTIFACT_DIR])
expect(mkdir_status).to_equal(0)  # oracle: pinned constant asserted by this scenario
val retained_assembly = VULKAN_COMPILER_ARTIFACT_DIR + "/processing_fill_rect.spvasm"
val retained_binary = VULKAN_COMPILER_ARTIFACT_DIR + "/processing_fill_rect.spv"
expect(rt_file_write_text(retained_assembly, assembly)).to_equal(true)
expect(rt_file_write_bytes(retained_binary, spirv)).to_equal(true)
val (artifact_sha_out, artifact_sha_err, artifact_sha_status) = rt_process_run("sha256sum", [retained_binary])
expect(artifact_sha_status).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(artifact_sha_err).to_equal("")
val artifact_sha = artifact_sha_out.split(" ")[0]
expect(artifact_sha.len()).to_equal(64)  # oracle: pinned constant asserted by this scenario
val receipt = "version=1\ncommand=bin/simple test test/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.spl --mode=interpreter --no-session-daemon\nevidence_class=physical-device\ncompiler=simple-vulkan-mir-backend\nassembler=spirv-as --target-env vulkan1.3\nvalidator=spirv-val --target-env vulkan1.3\nentry_point=processing_fill_rect_u32\nartifact_path=" + retained_binary + "\nartifact_sha256=" + artifact_sha + "\ndevice_name=" + session.device_name + "\ndevice_type=" + session.device_type + "\ndriver_identity=" + session.driver_identity + "\nreadback_bytes=" + readback.len().to_text() + "\nmismatch_count=" + mismatch_count.to_text() + "\nparity=pass\n"
expect(receipt).to_contain("compiler=simple-vulkan-mir-backend")
expect(receipt).to_contain("validator=spirv-val --target-env vulkan1.3")
expect(receipt).to_contain("mismatch_count=0")
val receipt_path = VULKAN_COMPILER_ARTIFACT_DIR + "/compiler_fill_rect_vulkan.receipt"
expect(rt_file_write_text(receipt_path, receipt)).to_equal(true)
print("processing_fill_rect_artifact_sha256=" + artifact_sha)
print("processing_fill_rect_receipt=" + receipt_path)

if output > 0:
    expect(vulkan_sffi_free_buffer(output)).to_equal(true)
if pipeline > 0:
    expect(vulkan_sffi_destroy_pipeline(pipeline)).to_equal(true)
if shader > 0:
    expect(vulkan_sffi_destroy_shader(shader)).to_equal(true)
session.release()
expect(vulkan_sffi_shutdown_reaped()).to_equal(true)
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

- Canonical SPipe generation for source `fef92429451acace47527177ca7b3791c2a3fdbebf77b8f6c981e40ebc6c8c31`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fef92429451acace47527177ca7b3791c2a3fdbebf77b8f6c981e40ebc6c8c31`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fef92429451acace47527177ca7b3791c2a3fdbebf77b8f6c981e40ebc6c8c31`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.spl
mirror: doc/06_spec/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass spirv-val and return exact physical-device pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
