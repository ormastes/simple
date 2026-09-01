# Cuda Shared Pointer Space Source Specification

> Tests covering CUDA shared pointer space source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Shared Pointer Space Source Specification

## Scenarios

### CUDA shared pointer space source contract

#### tracks pointer spaces per function and propagates them through pointer values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks pointer spaces per function and propagates them through pointer values


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks pointer spaces per function and propagates them through pointer values")
val source = cuda_backend_source()
expect(source).to_contain("pointer_spaces: Dict<i64, MemorySpace>")
expect(source).to_contain("self.pointer_spaces = {}")
expect(source).to_contain("self.pointer_spaces[local.id.id] = MemorySpace.Global")
expect(source).to_contain("self.compile_instruction(builder, inst, func)")
expect(source).to_contain("self.pointer_spaces[dest.id] = MemorySpace.Shared")
expect(source).to_contain("self.pointer_spaces[dest.id] = MemorySpace.Local")
expect(source).to_contain("self.propagate_pointer_space(dest, MirOperand.copy(src))")
expect(source).to_contain("self.propagate_pointer_space(dest, MirOperand.move(src))")
expect(source).to_contain("self.propagate_pointer_space(dest, operand)")
expect(source).to_contain("self.pointer_spaces[dest.id] = base_space")
```

</details>

#### selects pointer space for loads stores MIR atomics and atomic intrinsics

- selects pointer space for loads stores MIR atomics and atomic intrinsics


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects pointer space for loads stores MIR atomics and atomic intrinsics")
val source = cuda_backend_source()
expect(source).to_contain("self.pointer_memory_space(ptr, self.pointer_spaces)?")
expect(source).to_contain("self.atomic_memory_space(ptr, self.pointer_spaces)?")
expect(source).to_contain("self.compile_intrinsic(builder, dest, name, args, func, self.pointer_spaces)")
expect(source).to_contain("self.atomic_memory_space(args[0], pointer_spaces)?")
expect(source).to_contain("self.validate_typed_atomic_intrinsic(func, dest, args")
expect(source).to_contain("CUDA typed atomic destination type does not match intrinsic")
expect(source).to_contain("CUDA F32 vector memory intrinsic requires an F32 pointer")
expect(source).to_contain("CUDA F32 vector memory intrinsic index must be U64")
expect(source).to_contain("CUDA vector loads require MIR vector result lowering")
expect(source).to_contain("if arg_count != required_args:")
expect(source).to_contain("if not requires_dest and dest.?:")
expect(source).to_contain("val space_vs4 = self.type_mapper.ptx_state_space")
expect(source).to_contain("val space_vs2 = self.type_mapper.ptx_state_space")
expect(source).to_contain("self.memory_address_reg(builder")
```

</details>

#### rejects untracked pointers and local-memory atomics

- rejects untracked pointers and local-memory atomics


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects untracked pointers and local-memory atomics")
val source = cuda_backend_source()
val start = source.find("fn pointer_memory_space(")
val finish = source.find("me propagate_pointer_space(")
expect(start).to_be_greater_than(-1)
expect(finish).to_be_greater_than(start)
val helper = source.substring(start, finish)
expect(helper).to_contain("pointer has no memory-space provenance")
expect(helper).to_contain("atomics require global or shared memory")
expect(source).to_contain("cvta.to.shared.u64")
expect(source).to_contain("CUDA multi-block shared/local pointer provenance requires CFG dataflow lowering")
expect(source).to_contain("CUDA atomic CAS operands and result must match pointer element type")
expect(source).to_contain("CUDA shared allocation type must match destination pointer element type")
expect(source).to_contain("CUDA local allocation type must match destination pointer element type")
expect(source).to_contain("type_bindings: {}, layout_phase: nil, is_kernel: true")
expect(source).to_contain("gpu_target: \"cuda\", gpu_backend_order: \"cuda\"")
expect(source).to_contain("self.compile_function_with_kind(builder, func, true)")
expect(source).to_contain("self.compile_function_with_kind(builder, func, false)")
expect(source).to_contain("func.is_kernel")
```

</details>

#### uses PTX bit-width suffixes for CAS exchange and bitwise atomics

- uses PTX bit-width suffixes for CAS exchange and bitwise atomics


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses PTX bit-width suffixes for CAS exchange and bitwise atomics")
val source = ptx_builder_source()
expect(source).to_contain("me emit_atomic_cas")
expect(source).to_contain("me emit_atomic_exch")
expect(source).to_contain("me emit_atomic_and")
expect(source).to_contain("me emit_atomic_or")
expect(source).to_contain("me emit_atomic_xor")
expect(source).to_contain("self.atomic_bit_type(ty)")
expect(source).to_contain("case I64 | U64 | F64:")
expect(source).to_contain("val atomic_ty = if ty == PrimitiveType.I64: \".u64\"")
expect(source).to_not_contain(".and.b64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CUDA shared pointer space source contract.
- CUDA shared pointer space source contract

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `19e65278f218675cab06578bff58d9cc10a5b9baedb951d3d2ea42ff78fc1244`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19e65278f218675cab06578bff58d9cc10a5b9baedb951d3d2ea42ff78fc1244`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19e65278f218675cab06578bff58d9cc10a5b9baedb951d3d2ea42ff78fc1244`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks pointer spaces per function and propagates them through pointer values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects pointer space for loads stores MIR atomics and atomic intrinsics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cuda_shared_pointer_space_source_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects untracked pointers and local-memory atomics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
