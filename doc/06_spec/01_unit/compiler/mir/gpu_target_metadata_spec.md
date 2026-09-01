# Gpu Target Metadata Specification

> Tests covering MIR GPU target metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Target Metadata Specification

## Scenarios

### MIR GPU target metadata

#### lowers frontend-shaped gpu attribute metadata into MIR

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers frontend-shaped gpu attribute metadata into MIR
   - Expected: result.is_kernel is true
   - Expected: result.gpu_target equals `opencl`
   - Expected: result.gpu_backend_order equals `opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers frontend-shaped gpu attribute metadata into MIR")
val parsed_attr = parse_function_attrs([make_gpu_source_attr("opencl")])
val lowerer = MirLowering.new(SymbolTable.new())
val fn_ = make_mir_function("gpu_kernel")

val result = lowerer.apply_function_attr_to_mir(fn_, parsed_attr)

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### propagates normalized OpenCL target metadata from function attrs

- propagates normalized OpenCL target metadata from function attrs
   - Expected: result.is_kernel is true
   - Expected: result.gpu_target equals `opencl`
   - Expected: result.gpu_backend_order equals `opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("propagates normalized OpenCL target metadata from function attrs")
val lowerer = MirLowering.new(SymbolTable.new())
val fn_ = make_mir_function("gpu_kernel")
val attr = make_gpu_attr("opencl-spirv", "")

val result = lowerer.apply_function_attr_to_mir(fn_, attr)

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### propagates normalized ROCm target metadata as HIP from function attrs

- propagates normalized ROCm target metadata as HIP from function attrs
   - Expected: result.is_kernel is true
   - Expected: result.gpu_target equals `hip`
   - Expected: result.gpu_backend_order equals `hip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("propagates normalized ROCm target metadata as HIP from function attrs")
val lowerer = MirLowering.new(SymbolTable.new())
val fn_ = make_mir_function("gpu_kernel")
val attr = make_gpu_attr("rocm", "")

val result = lowerer.apply_function_attr_to_mir(fn_, attr)

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("hip")
expect(result.gpu_backend_order).to_equal("hip")
```

</details>

#### preserves canonical explicit backend order through MirFunction copies

- preserves canonical explicit backend order through MirFunction copies
   - Expected: copied.is_kernel is true
   - Expected: copied.gpu_target equals `auto`
   - Expected: copied.gpu_backend_order equals `hip,opencl,cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves canonical explicit backend order through MirFunction copies")
val fn_ = make_mir_function("gpu_kernel")
val attr = parse_function_attrs([make_gpu_source_attr_with_backends("auto", "rocm,cl,cuda")])
val lowerer = MirLowering.new(SymbolTable.new())
val tagged = lowerer.apply_function_attr_to_mir(fn_, attr)

val copied = MirFunction.with_blocks(tagged, [empty_block("replacement")])

expect(copied.is_kernel).to_equal(true)
expect(copied.gpu_target).to_equal("auto")
expect(copied.gpu_backend_order).to_equal("hip,opencl,cuda")
```

</details>

#### canonicalizes explicit backend order metadata through common aliases

- canonicalizes explicit backend order metadata through common aliases
   - Expected: normalize_gpu_backend_order_metadata("rocm, cl, nvptx") equals `hip,opencl,cuda`
   - Expected: result.gpu_target equals `auto`
   - Expected: result.gpu_backend_order equals `hip,opencl,cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("canonicalizes explicit backend order metadata through common aliases")
expect(normalize_gpu_backend_order_metadata("rocm, cl, nvptx")).to_equal("hip,opencl,cuda")

val fn_ = make_mir_function("gpu_kernel")
val attr = make_gpu_attr("auto", " hip-cpp, opencl-spirv, ptx ")
val lowerer = MirLowering.new(SymbolTable.new())

val result = lowerer.apply_function_attr_to_mir(fn_, attr)

expect(result.gpu_target).to_equal("auto")
expect(result.gpu_backend_order).to_equal("hip,opencl,cuda")
```

</details>

#### preserves positional GPU target metadata through HIR and MIR lowering

- preserves positional GPU target metadata through HIR and MIR lowering
   - Expected: result.is_kernel is true
   - Expected: result.gpu_target equals `opencl`
   - Expected: result.gpu_backend_order equals `opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves positional GPU target metadata through HIR and MIR lowering")
val attr = parse_function_attrs([make_gpu_source_attr("opencl")])

val result = lower_hir_attr_function_to_mir(attr, "positional_opencl_kernel")

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### preserves named GPU target metadata through HIR and MIR lowering

- preserves named GPU target metadata through HIR and MIR lowering
   - Expected: result.is_kernel is true
   - Expected: result.gpu_target equals `opencl`
   - Expected: result.gpu_backend_order equals `opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves named GPU target metadata through HIR and MIR lowering")
val attr = parse_function_attrs([make_gpu_source_attr_with_backends("opencl", "")])

val result = lower_hir_attr_function_to_mir(attr, "named_opencl_kernel")

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### preserves named GPU backend order metadata through HIR and MIR lowering

- preserves named GPU backend order metadata through HIR and MIR lowering
   - Expected: result.is_kernel is true
   - Expected: result.gpu_target equals `auto`
   - Expected: result.gpu_backend_order equals `hip,opencl,cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves named GPU backend order metadata through HIR and MIR lowering")
val attr = parse_function_attrs([make_gpu_source_attr_with_backends("auto", "rocm,cl,cuda")])

val result = lower_hir_attr_function_to_mir(attr, "ordered_gpu_kernel")

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("auto")
expect(result.gpu_backend_order).to_equal("hip,opencl,cuda")
```

</details>

#### preserves GPU metadata through complete module lowering

- preserves GPU metadata through complete module lowering
   - Expected: hir.gpu_function_targets.has("kernel") is true
   - Expected: hir.gpu_function_targets["kernel"] equals `auto`
   - Expected: hir.gpu_function_backend_orders["kernel"] equals `rocm,cl,cuda`
   - Expected: hir.symbols.has_gpu_function_metadata("kernel") is true
   - Expected: hir.symbols.gpu_function_target("kernel") equals `auto`
   - Expected: hir.symbols.gpu_function_backend_order("kernel") equals `rocm,cl,cuda`
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: result.is_kernel is true
   - Expected: result.gpu_target equals `auto`
   - Expected: result.gpu_backend_order equals `hip,opencl,cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves GPU metadata through complete module lowering")
val source = "@gpu(target=\"auto\", backends=\"rocm,cl,cuda\")\nfn kernel(input: [u32]) -> ():\n    ()\n"
val parsed = parse_full_frontend(source, "gpu_metadata_module.spl", "gpu_metadata_module", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("gpu_metadata_module.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir.gpu_function_targets.has("kernel")).to_equal(true)
expect(hir.gpu_function_targets["kernel"]).to_equal("auto")
expect(hir.gpu_function_backend_orders["kernel"]).to_equal("rocm,cl,cuda")
expect(hir.symbols.has_gpu_function_metadata("kernel")).to_equal(true)
expect(hir.symbols.gpu_function_target("kernel")).to_equal("auto")
expect(hir.symbols.gpu_function_backend_order("kernel")).to_equal("rocm,cl,cuda")
val mir = MirLowering.new(hir.symbols).lower_module(hir)
val result = mir.functions.values()[0]

expect(hir_lowering.errors.len()).to_equal(0)
expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("auto")
expect(result.gpu_backend_order).to_equal("hip,opencl,cuda")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/gpu_target_metadata_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR GPU target metadata.
- MIR GPU target metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `95ab9645267824a6e49ea19bac86898afcb6852c80e66b7509f69de984ff348c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95ab9645267824a6e49ea19bac86898afcb6852c80e66b7509f69de984ff348c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95ab9645267824a6e49ea19bac86898afcb6852c80e66b7509f69de984ff348c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/mir/gpu_target_metadata_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/gpu_target_metadata_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/gpu_target_metadata_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/gpu_target_metadata_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/gpu_target_metadata_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/gpu_target_metadata_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers frontend-shaped gpu attribute metadata into MIR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/gpu_target_metadata_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates normalized OpenCL target metadata from function attrs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/gpu_target_metadata_spec.spl:176:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates normalized ROCm target metadata as HIP from function attrs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
