# Vhdl Kernel Entity Contract Specification

> Tests covering VHDL kernel entity contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Kernel Entity Contract Specification

## Scenarios

### VHDL kernel entity contract

#### accepts a vhdl-targeted kernel and rejects non-kernel and opencl functions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a vhdl-targeted kernel and rejects non-kernel and opencl functions
   - Expected: vhdl_kernel_accepts(vhdl_fn) is true
   - Expected: vhdl_kernel_accepts(non_kernel) is false
   - Expected: vhdl_kernel_accepts(opencl_fn) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a vhdl-targeted kernel and rejects non-kernel and opencl functions")
val vhdl_fn = make_vhdl_scalar_kernel()
val non_kernel = make_non_kernel(10, "regular_fn")
val opencl_fn = make_opencl_kernel(11, "opencl_fn")

expect(vhdl_kernel_accepts(vhdl_fn)).to_equal(true)
expect(vhdl_kernel_accepts(non_kernel)).to_equal(false)
expect(vhdl_kernel_accepts(opencl_fn)).to_equal(false)
```

</details>

#### plan_module counts accepted vhdl kernels correctly

- plan_module counts accepted vhdl kernels correctly
   - Expected: plan.accepted_kernel_count equals `2`
   - Expected: plan.rejected_kernel_count equals `0`
   - Expected: plan.ready is true
   - Expected: plan.backend_name equals `vhdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("plan_module counts accepted vhdl kernels correctly")
val module = make_module([make_vhdl_scalar_kernel(), make_vhdl_vector_add_kernel(), make_opencl_kernel(11, "opencl_fn")])
val plan = vhdl_kernel_plan_module(module)

expect(plan.accepted_kernel_count).to_equal(2)
expect(plan.rejected_kernel_count).to_equal(0)
expect(plan.ready).to_equal(true)
expect(plan.backend_name).to_equal("vhdl")
```

</details>

#### emits entity declaration with entity keyword for scalar kernel

- emits entity declaration with entity keyword for scalar kernel
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits entity declaration with entity keyword for scalar kernel")
val func = make_vhdl_scalar_kernel()
val result = emit_vhdl_kernel_entity(func)

expect(result.is_ok()).to_equal(true)
val source = result.unwrap()
expect(source).to_contain("entity vhdl_scale_u32 is")
expect(source).to_contain("end entity vhdl_scale_u32;")
```

</details>

#### emits standard control ports clk rst ndrange_size done_out

- emits standard control ports clk rst ndrange_size done_out


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits standard control ports clk rst ndrange_size done_out")
val func = make_vhdl_scalar_kernel()
val source = emit_vhdl_kernel_entity(func).unwrap()

expect(source).to_contain("clk : in bit")
expect(source).to_contain("rst : in bit")
expect(source).to_contain("ndrange_size : in unsigned(31 downto 0)")
expect(source).to_contain("done_out : out bit")
```

</details>

#### emits scalar parameter as input port

- emits scalar parameter as input port


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits scalar parameter as input port")
val func = make_vhdl_scalar_kernel()
val source = emit_vhdl_kernel_entity(func).unwrap()

expect(source).to_contain("n : in unsigned(31 downto 0)")
expect(source).to_contain("factor : in unsigned(31 downto 0)")
```

</details>

#### emits pointer parameter as memory-interface ports

- emits pointer parameter as memory-interface ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits pointer parameter as memory-interface ports")
val func = make_vhdl_vector_add_kernel()
val source = emit_vhdl_kernel_entity(func).unwrap()

expect(source).to_contain("a_addr_out : out unsigned(31 downto 0)")
expect(source).to_contain("a_data_in : in unsigned(31 downto 0)")
expect(source).to_contain("a_data_out : out unsigned(31 downto 0)")
expect(source).to_contain("a_we_out : out bit")
```

</details>

<details>
<summary>Advanced: emits counter-driven loop process in architecture body</summary>

#### emits counter-driven loop process in architecture body

- emits counter-driven loop process in architecture body


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits counter-driven loop process in architecture body")
val func = make_vhdl_scalar_kernel()
val source = emit_vhdl_kernel_entity(func).unwrap()

expect(source).to_contain("architecture rtl of vhdl_scale_u32 is")
expect(source).to_contain("kernel_loop")
expect(source).to_contain("work_counter")
expect(source).to_contain("ndrange_size")
expect(source).to_contain("end architecture rtl;")
```

</details>


</details>

#### emits architecture for no-param kernel

- emits architecture for no-param kernel
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits architecture for no-param kernel")
val func = make_vhdl_no_param_kernel()
val result = emit_vhdl_kernel_entity(func)

expect(result.is_ok()).to_equal(true)
val source = result.unwrap()
expect(source).to_contain("entity vhdl_noop is")
expect(source).to_contain("done_out : out bit")
expect(source).to_contain("architecture rtl of vhdl_noop is")
```

</details>

#### rejects a kernel with gpu_syncthreads (GpuBarrier) fail closed

- rejects a kernel with gpu_syncthreads (GpuBarrier) fail closed
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a kernel with gpu_syncthreads (GpuBarrier) fail closed")
val func = make_vhdl_barrier_kernel()
val result = emit_vhdl_kernel_entity(func)

expect(result.is_err()).to_equal(true)
val msg = result.unwrap_err().message
expect(msg).to_contain("VHDL-KERNEL-UNSUPPORTED")
expect(msg).to_contain("gpu_syncthreads")
```

</details>

#### rejects a kernel with gpu_shared_mem (GpuSharedAlloc) fail closed

- rejects a kernel with gpu_shared_mem (GpuSharedAlloc) fail closed
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a kernel with gpu_shared_mem (GpuSharedAlloc) fail closed")
val func = make_vhdl_shared_alloc_kernel()
val result = emit_vhdl_kernel_entity(func)

expect(result.is_err()).to_equal(true)
val msg = result.unwrap_err().message
expect(msg).to_contain("VHDL-KERNEL-UNSUPPORTED")
expect(msg).to_contain("gpu_shared_mem")
```

</details>

#### rejects kernel with non-unit return type fail closed

- rejects kernel with non-unit return type fail closed
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects kernel with non-unit return type fail closed")
val bad_func = MirFunction(
    symbol: SymbolId(id: 99),
    name: "bad_return",
    signature: MirSignature(params: [], return_type: u32_type(), is_variadic: false),
    locals: [],
    blocks: [empty_kernel_block()],
    entry_block: BlockId.entry(),
    span: Span.empty(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: true,
    gpu_target: "vhdl",
    gpu_backend_order: "vhdl",
    is_export_c: false,
    export_name: "",
    has_driver_manifest_attr: false,
    driver_manifest_attr: nil,
    has_vhdl_metadata: false,
    vhdl_metadata: vhdl_hardware_metadata_default(),
    has_fast_math: false
)
val result = emit_vhdl_kernel_entity(bad_func)

expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-KERNEL-UNSUPPORTED")
```

</details>

#### emits each vhdl kernel entity independently (dict-key iteration workaround)

- emits each vhdl kernel entity independently (dict-key iteration workaround)
   - Expected: r1.is_ok() is true
   - Expected: r2.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits each vhdl kernel entity independently (dict-key iteration workaround)")
# Note: emit_vhdl_kernel_entities_for_module with Dict<SymbolId,MirFunction> only
# iterates one entry in interpreter mode (struct-key Dict iteration P2 bug).
# Contract: each kernel emits correctly when called directly.
val r1 = emit_vhdl_kernel_entity(make_vhdl_vector_add_kernel())
val r2 = emit_vhdl_kernel_entity(make_vhdl_scalar_kernel())

expect(r1.is_ok()).to_equal(true)
expect(r2.is_ok()).to_equal(true)
expect(r1.unwrap()).to_contain("entity vhdl_vector_add_u32 is")
expect(r2.unwrap()).to_contain("entity vhdl_scale_u32 is")
```

</details>

#### module emit returns ok for single vhdl kernel

- module emit returns ok for single vhdl kernel
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("module emit returns ok for single vhdl kernel")
# Single-entry Dict avoids the struct-key Dict iteration P2 bug.
val module = make_module([make_vhdl_vector_add_kernel()])
val result = emit_vhdl_kernel_entities_for_module(module)

expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_contain("entity vhdl_vector_add_u32 is")
```

</details>

#### module emission rejects if any kernel has unsupported construct

- module emission rejects if any kernel has unsupported construct
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("module emission rejects if any kernel has unsupported construct")
val module = make_module([make_vhdl_barrier_kernel()])
val result = emit_vhdl_kernel_entities_for_module(module)

expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-KERNEL-UNSUPPORTED")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL kernel entity contract.
- VHDL kernel entity contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `b594561486b7998ff4c80e43116db881b54939997d3a5eb5bc383a38d66914cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b594561486b7998ff4c80e43116db881b54939997d3a5eb5bc383a38d66914cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b594561486b7998ff4c80e43116db881b54939997d3a5eb5bc383a38d66914cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a vhdl-targeted kernel and rejects non-kernel and opencl functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plan_module counts accepted vhdl kernels correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl:194:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits entity declaration with entity keyword for scalar kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
