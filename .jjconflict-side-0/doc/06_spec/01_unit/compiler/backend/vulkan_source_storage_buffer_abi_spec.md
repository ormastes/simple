# Vulkan Source Storage Buffer Abi Specification

> Tests covering source Vulkan storage-buffer ABI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Source Storage Buffer Abi Specification

## Scenarios

### source Vulkan storage-buffer ABI

#### lowers a bounded [u32] copy kernel to StorageBuffer parameters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers a bounded [u32] copy kernel to StorageBuffer parameters
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: hir.gpu_function_targets.has("copy") is true
   - Expected: hir.symbols.has_gpu_function_metadata("copy") is true
   - Expected: hir.symbols.gpu_function_target("copy") equals `vulkan`
   - Expected: hir_module_gpu_target_count(hir) equals `1`
   - Expected: symbol_table_has_copy_gpu(hir.symbols) is true
   - Expected: hir_function_is_gpu(hir.functions.values()[0]) is true
   - Expected: hir_function_returns_unit(hir.functions.values()[0]) is true
   - Expected: mir_lowering.errors.len() equals `0`
   - Expected: fn_.is_kernel is true
   - Expected: fn_.gpu_target equals `vulkan`
   - Expected: fn_.signature.return_type.kind equals `MirTypeKind.Unit`
   - Expected: fn_.signature.params.len() equals `3`
   - Expected: rt_enum_discriminant(fn_.signature.params[0].kind) equals `ptr_disc`
   - Expected: rt_enum_discriminant(fn_.signature.params[1].kind) equals `ptr_disc`
   - Expected: rt_enum_discriminant(fn_.signature.params[2].kind) equals `u32_disc`
   - Expected: rt_enum_discriminant(fn_.locals[0].type_.kind) equals `ptr_disc`
   - Expected: rt_enum_discriminant(fn_.locals[1].type_.kind) equals `ptr_disc`
   - Expected: rt_enum_discriminant(fn_.locals[2].type_.kind) equals `u32_disc`
   - Expected: pointee.kind equals `MirTypeKind.U32`
   - Expected: mutable is false
   - Expected: false is true
   - Expected: pointee.kind equals `MirTypeKind.U32`
   - Expected: mutable is true
   - Expected: false is true
   - Expected: fn_.signature.params[2].kind equals `MirTypeKind.U32`
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a bounded [u32] copy kernel to StorageBuffer parameters")
val source = "@gpu(\"vulkan\")\n" +
    "fn copy(input: [u32], mut output: [u32], n: u32) -> ():\n" +
    "    val i = gpu_global_id(0)\n" +
    "    if i + 1 < n:\n" +
    "        output[i + 1] = input[i] + 1\n"
val parsed = parse_full_frontend(source, "vulkan_storage_buffer.spl", "vulkan_storage_buffer", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("vulkan_storage_buffer.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)
expect(hir.gpu_function_targets.has("copy")).to_equal(true)
expect(hir.symbols.has_gpu_function_metadata("copy")).to_equal(true)
expect(hir.symbols.gpu_function_target("copy")).to_equal("vulkan")
expect(hir_module_gpu_target_count(hir)).to_equal(1)
expect(symbol_table_has_copy_gpu(hir.symbols)).to_equal(true)
expect(hir_function_is_gpu(hir.functions.values()[0])).to_equal(true)
expect(hir_function_returns_unit(hir.functions.values()[0])).to_equal(true)
var mir_lowering = MirLowering.new(hir.symbols)
val mir = mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_equal(0)
val fn_ = mir.functions.values()[0]
expect(fn_.is_kernel).to_equal(true)
expect(fn_.gpu_target).to_equal("vulkan")
expect(fn_.signature.return_type.kind).to_equal(MirTypeKind.Unit)
expect(fn_.signature.params.len()).to_equal(3)
expect(fn_.locals.len()).to_be_greater_than(2)
val ptr_disc = 422722806  # hash("Ptr")
val u32_disc = 1163175990  # hash("U32")
expect(rt_enum_discriminant(fn_.signature.params[0].kind)).to_equal(ptr_disc)
expect(rt_enum_discriminant(fn_.signature.params[1].kind)).to_equal(ptr_disc)
expect(rt_enum_discriminant(fn_.signature.params[2].kind)).to_equal(u32_disc)
expect(rt_enum_discriminant(fn_.locals[0].type_.kind)).to_equal(ptr_disc)
expect(rt_enum_discriminant(fn_.locals[1].type_.kind)).to_equal(ptr_disc)
expect(rt_enum_discriminant(fn_.locals[2].type_.kind)).to_equal(u32_disc)
match fn_.signature.params[0].kind:
    case MirTypeKind.Ptr(pointee, mutable):
        expect(pointee.kind).to_equal(MirTypeKind.U32)
        expect(mutable).to_equal(false)
    case _:
        expect(false).to_equal(true)
match fn_.signature.params[1].kind:
    case MirTypeKind.Ptr(pointee, mutable):
        expect(pointee.kind).to_equal(MirTypeKind.U32)
        expect(mutable).to_equal(true)
    case _:
        expect(false).to_equal(true)
expect(fn_.signature.params[2].kind).to_equal(MirTypeKind.U32)
val result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(mir)
expect(result.is_ok()).to_equal(true)
val output = result.unwrap().text_output
val _written = rt_file_write_text("/tmp/simple_vulkan_source_storage_buffer.spvasm", output)
expect(output).to_contain("OpTypePointer StorageBuffer")
expect(output).to_contain("DescriptorSet 0")
expect(output).to_contain("Binding 0")
expect(output).to_contain("Binding 1")
expect(output).to_contain("OpAccessChain")
expect(output).to_contain("OpLoad")
expect(output).to_contain("OpStore")
```

</details>

#### rejects source buffer elements outside the Vulkan U32 ABI

- rejects source buffer elements outside the Vulkan U32 ABI
   - Expected: hir_lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects source buffer elements outside the Vulkan U32 ABI")
val source = "@gpu(\"vulkan\")\n" +
    "fn copy(input: [i32], mut output: [u32], n: u32) -> ():\n" +
    "    ()\n"
val parsed = parse_full_frontend(source, "vulkan_storage_buffer_bad.spl", "vulkan_storage_buffer_bad", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("vulkan_storage_buffer_bad.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(hir.symbols)
mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_be_greater_than(0)
expect(mir_lowering.errors[0].message).to_contain("require U32 elements")
```

</details>

#### rejects writes through immutable source buffers

- rejects writes through immutable source buffers
   - Expected: hir_lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects writes through immutable source buffers")
val source = "@gpu(\"vulkan\")\n" +
    "fn copy(input: [u32], n: u32) -> ():\n" +
    "    input[gpu_global_id(0)] = n\n"
val parsed = parse_full_frontend(source, "vulkan_storage_buffer_immutable.spl", "vulkan_storage_buffer_immutable", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("vulkan_storage_buffer_immutable.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(hir.symbols)
mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_be_greater_than(0)
expect(mir_lowering.errors[0].message).to_contain("immutable Vulkan storage buffer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering source Vulkan storage-buffer ABI.
- source Vulkan storage-buffer ABI

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b31faa84b016b6cfc0dc98c4267092f0d0da8af7f43e4736eb50eae1c6255b5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b31faa84b016b6cfc0dc98c4267092f0d0da8af7f43e4736eb50eae1c6255b5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b31faa84b016b6cfc0dc98c4267092f0d0da8af7f43e4736eb50eae1c6255b5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a bounded [u32] copy kernel to StorageBuffer parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects source buffer elements outside the Vulkan U32 ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects writes through immutable source buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
