# Cuda Source Global Pointer Abi Specification

> Tests covering source CUDA global-pointer ABI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Source Global Pointer Abi Specification

## Scenarios

### source CUDA global-pointer ABI

#### lowers a bounded u32 fill kernel to global pointer PTX

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers a bounded u32 fill kernel to global pointer PTX
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: mir_lowering.errors.len() equals `0`
   - Expected: function.is_kernel is true
   - Expected: function.gpu_target equals `cuda`
   - Expected: rt_enum_discriminant(function.signature.params[0].kind) equals `ptr_disc`
   - Expected: rt_enum_discriminant(function.signature.params[1].kind) equals `u32_disc`
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a bounded u32 fill kernel to global pointer PTX")
val source = "@gpu(\"cuda\")\n" +
    "fn fill(mut output: [u32], n: u32) -> ():\n" +
    "    val i = gpu_global_id(0)\n" +
    "    if i < n:\n" +
    "        output[i] = 42u32\n"
val parsed = parse_full_frontend(source, "cuda_global_pointer.spl", "cuda_global_pointer", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("cuda_global_pointer.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)

var mir_lowering = MirLowering.new(hir.symbols)
val mir = mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_equal(0)
val function = mir.functions.values()[0]
val ptr_disc = 422722806
val u32_disc = 1163175990
expect(function.is_kernel).to_equal(true)
expect(function.gpu_target).to_equal("cuda")
expect(rt_enum_discriminant(function.signature.params[0].kind)).to_equal(ptr_disc)
expect(rt_enum_discriminant(function.signature.params[1].kind)).to_equal(u32_disc)

val result = CudaBackend.create((8, 6)).compile(mir)
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain(".visible .entry fill")
expect(ptx).to_contain(".param .u64 param_0")
expect(ptx).to_contain("st.global.u32")
```

</details>

#### rejects writes through immutable CUDA global buffers

- rejects writes through immutable CUDA global buffers
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: mir_lowering.errors[0].message equals `cannot write through an immutable CUDA global buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects writes through immutable CUDA global buffers")
val source = "@gpu(\"cuda\")\n" +
    "fn fill(output: [u32], n: u32) -> ():\n" +
    "    output[gpu_global_id(0)] = n\n"
val parsed = parse_full_frontend(source, "cuda_global_pointer_immutable.spl", "cuda_global_pointer_immutable", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("cuda_global_pointer_immutable.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(hir.symbols)
mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_be_greater_than(0)
expect(mir_lowering.errors[0].message).to_equal("cannot write through an immutable CUDA global buffer")
```

</details>

#### loads CUDA global pointers directly without host array calls

- loads CUDA global pointers directly without host array calls
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: mir_lowering.errors.len() equals `0`
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads CUDA global pointers directly without host array calls")
val source = "@gpu(\"cuda\")\n" +
    "fn read(input: [u32], n: u32) -> ():\n" +
    "    val i = gpu_global_id(0)\n" +
    "    if i < n:\n" +
    "        val x = input[i]\n"
val parsed = parse_full_frontend(source, "cuda_global_pointer_read.spl", "cuda_global_pointer_read", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("cuda_global_pointer_read.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(hir.symbols)
val mir = mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_equal(0)
val result = CudaBackend.create((8, 6)).compile(mir)
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("ld.global.u32")
expect(ptx).to_not_contain("rt_array_get")
expect(ptx).to_not_contain("rt_array_len")
expect(ptx).to_not_contain("rt_array_set")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering source CUDA global-pointer ABI.
- source CUDA global-pointer ABI

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

- Canonical SPipe generation for source `5f694834eadf8091e3fd82701d6a942e68024a909e3fee5cd65a7065485eb9f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f694834eadf8091e3fd82701d6a942e68024a909e3fee5cd65a7065485eb9f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f694834eadf8091e3fd82701d6a942e68024a909e3fee5cd65a7065485eb9f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a bounded u32 fill kernel to global pointer PTX' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects writes through immutable CUDA global buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads CUDA global pointers directly without host array calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
