# vulkan_compiler_spirv_live_qualification_spec

> Strict Vulkan launch/readback qualification for compiler-produced SPIR-V.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_compiler_spirv_live_qualification_spec

Strict Vulkan launch/readback qualification for compiler-produced SPIR-V.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/vulkan_compiler_spirv_live_qualification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Strict Vulkan launch/readback qualification for compiler-produced SPIR-V.

The Simple Vulkan backend emits SPIR-V assembly. This test assembles that exact
source->HIR->MIR producer output, then passes the resulting binary to the
runtime's Vulkan SPIR-V module API for a real storage-buffer dispatch.

@tag: integration, rendering, vulkan, hardware, strict

## Scenarios

### compiler-produced Vulkan SPIR-V live qualification

#### writes exact U32 values through binding zero and a U32 push constant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes exact U32 values through binding zero and a U32 push constant
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: mir_lowering.errors.len() equals `0`
   - Expected: compiled.is_ok() is true
   - Expected: assembly_written is true
   - Expected: tools_status equals `0`
   - Expected: as_status equals `0`
   - Expected: as_err equals ``
   - Expected: val_status equals `0`
   - Expected: val_err equals ``
   - Expected: session.init() equals `0`
   - Expected: session.device_type == "discrete" or session.device_type == "integrated" is true
   - Expected: uploaded is true
   - Expected: readback equals `expected`
   - Expected: vulkan_read_u32_le(readback, index * 4) equals `42`
   - Expected: freed is true
   - Expected: pipeline_destroyed is true
   - Expected: shader_destroyed is true
   - Expected: shutdown_reaped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 92 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes exact U32 values through binding zero and a U32 push constant")
val source = "@gpu(\"vulkan\")\n" +
    "fn fill(mut output: [u32], n: u32) -> ():\n" +
    "    val i = gpu_global_id(0)\n" +
    "    if i < n:\n" +
    "        output[i] = 42u32\n"
val parsed = parse_full_frontend(source, "vulkan_compiler_spirv_live.spl", "vulkan_compiler_spirv_live", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("vulkan_compiler_spirv_live.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(hir.symbols)
val mir = mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_equal(0)

val compiled = vulkan_compile_module_direct(mir)
expect(compiled.is_ok()).to_equal(true)
val assembly = compiled.unwrap().text_output
expect(assembly).to_contain("; Generator: Simple Compiler")
expect(assembly).to_contain("Binding 0")
expect(assembly).to_contain("PushConstant")

val assembly_path = "/tmp/simple_vulkan_compiler_spirv_live.spvasm"
val binary_path = "/tmp/simple_vulkan_compiler_spirv_live.spv"
val assembly_written = rt_file_write_text(assembly_path, assembly)
print("vulkan_compiler_live_assembly_written=" + assembly_written.to_text())
expect(assembly_written).to_equal(true)
val (_which_out, _which_err, tools_status) = rt_process_run(
    "/bin/sh", ["-c", "command -v spirv-as >/dev/null 2>&1 && command -v spirv-val >/dev/null 2>&1"])
expect(tools_status).to_equal(0)
val (_as_out, as_err, as_status) = rt_process_run(
    "spirv-as", ["--target-env", "vulkan1.3", assembly_path, "-o", binary_path])
expect(as_status).to_equal(0)
expect(as_err).to_equal("")
val (_val_out, val_err, val_status) = rt_process_run(
    "spirv-val", ["--target-env", "vulkan1.3", binary_path])
expect(val_status).to_equal(0)
expect(val_err).to_equal("")
val spirv = rt_file_read_bytes(binary_path)
expect(spirv.len()).to_be_greater_than(20)

var session = VulkanSession.create()
expect(session.init()).to_equal(0)
print("vulkan_compiler_live_device_name=" + session.device_name)
print("vulkan_compiler_live_device_type=" + session.device_type)
print("vulkan_compiler_live_driver_identity=" + session.driver_identity)
expect(session.device_name.len()).to_be_greater_than(0)
expect(session.driver_identity.len()).to_be_greater_than(0)
expect(session.device_type == "discrete" or session.device_type == "integrated").to_equal(true)
val shader = vulkan_sffi_compile_spirv(spirv)
expect(shader).to_be_greater_than(0)
val pipeline = vulkan_sffi_create_compute_pipeline(shader, "fill", 4)
expect(pipeline).to_be_greater_than(0)
val count: i64 = 8
val output = vulkan_sffi_alloc_buffer(count * 4, 0x80)
expect(output).to_be_greater_than(0)
if shader > 0 and pipeline > 0 and output > 0:
    val zeroes: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
    val uploaded = vulkan_sffi_copy_to_buffer(output, zeroes, 0)
    print("vulkan_compiler_live_uploaded=" + uploaded.to_text())
    expect(uploaded).to_equal(true)
    expect(vulkan_dispatch_framebuffer_compute_checked(
        output, pipeline, vulkan_u32_le(count), 1, 1, 1)).to_equal(1)
    val expected: [u8] = [42u8, 0u8, 0u8, 0u8, 42u8, 0u8, 0u8, 0u8,
        42u8, 0u8, 0u8, 0u8, 42u8, 0u8, 0u8, 0u8,
        42u8, 0u8, 0u8, 0u8, 42u8, 0u8, 0u8, 0u8,
        42u8, 0u8, 0u8, 0u8, 42u8, 0u8, 0u8, 0u8]
    val readback = vulkan_sffi_read_buffer_bytes(output, count * 4, 0)
    expect(readback).to_equal(expected)
    var index: i64 = 0
    while index < count:
        expect(vulkan_read_u32_le(readback, index * 4)).to_equal(42)
        index = index + 1
if output > 0:
    val freed = vulkan_sffi_free_buffer(output)
    print("vulkan_compiler_live_buffer_freed=" + freed.to_text())
    expect(freed).to_equal(true)
if pipeline > 0:
    val pipeline_destroyed = vulkan_sffi_destroy_pipeline(pipeline)
    print("vulkan_compiler_live_pipeline_destroyed=" + pipeline_destroyed.to_text())
    expect(pipeline_destroyed).to_equal(true)
if shader > 0:
    val shader_destroyed = vulkan_sffi_destroy_shader(shader)
    print("vulkan_compiler_live_shader_destroyed=" + shader_destroyed.to_text())
    expect(shader_destroyed).to_equal(true)
session.release()
val shutdown_reaped = vulkan_sffi_shutdown_reaped()
print("vulkan_compiler_live_shutdown_reaped=" + shutdown_reaped.to_text())
expect(shutdown_reaped).to_equal(true)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4be60af3102303a3b2b6bc02cfaebb3c8ea41500e93755a078033fd515f1cb27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4be60af3102303a3b2b6bc02cfaebb3c8ea41500e93755a078033fd515f1cb27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4be60af3102303a3b2b6bc02cfaebb3c8ea41500e93755a078033fd515f1cb27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/rendering/vulkan_compiler_spirv_live_qualification_spec.spl
mirror: doc/06_spec/02_integration/rendering/vulkan_compiler_spirv_live_qualification_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/vulkan_compiler_spirv_live_qualification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/vulkan_compiler_spirv_live_qualification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/vulkan_compiler_spirv_live_qualification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/vulkan_compiler_spirv_live_qualification_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes exact U32 values through binding zero and a U32 push constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
