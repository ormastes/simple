# Vhdl Kernel Entity Contract Specification

> <details>

<!-- sdn-diagram:id=vhdl_kernel_entity_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_kernel_entity_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_kernel_entity_contract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_kernel_entity_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Kernel Entity Contract Specification

## Scenarios

### VHDL kernel entity contract

#### accepts a vhdl-targeted kernel and rejects non-kernel and opencl functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl_fn = make_vhdl_scalar_kernel()
val non_kernel = make_non_kernel(10, "regular_fn")
val opencl_fn = make_opencl_kernel(11, "opencl_fn")

expect(vhdl_kernel_accepts(vhdl_fn)).to_equal(true)
expect(vhdl_kernel_accepts(non_kernel)).to_equal(false)
expect(vhdl_kernel_accepts(opencl_fn)).to_equal(false)
```

</details>

#### plan_module counts accepted vhdl kernels correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_module([make_vhdl_scalar_kernel(), make_vhdl_vector_add_kernel(), make_opencl_kernel(11, "opencl_fn")])
val plan = vhdl_kernel_plan_module(module)

expect(plan.accepted_kernel_count).to_equal(2)
expect(plan.rejected_kernel_count).to_equal(0)
expect(plan.ready).to_equal(true)
expect(plan.backend_name).to_equal("vhdl")
```

</details>

#### emits entity declaration with entity keyword for scalar kernel

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_vhdl_scalar_kernel()
val result = emit_vhdl_kernel_entity(func)

expect(result.is_ok()).to_equal(true)
val source = result.unwrap()
expect(source).to_contain("entity vhdl_scale_u32 is")
expect(source).to_contain("end entity vhdl_scale_u32;")
```

</details>

#### emits standard control ports clk rst ndrange_size done_out

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_vhdl_scalar_kernel()
val source = emit_vhdl_kernel_entity(func).unwrap()

expect(source).to_contain("clk : in bit")
expect(source).to_contain("rst : in bit")
expect(source).to_contain("ndrange_size : in unsigned(31 downto 0)")
expect(source).to_contain("done_out : out bit")
```

</details>

#### emits scalar parameter as input port

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_vhdl_scalar_kernel()
val source = emit_vhdl_kernel_entity(func).unwrap()

expect(source).to_contain("n : in unsigned(31 downto 0)")
expect(source).to_contain("factor : in unsigned(31 downto 0)")
```

</details>

#### emits pointer parameter as memory-interface ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_vhdl_barrier_kernel()
val result = emit_vhdl_kernel_entity(func)

expect(result.is_err()).to_equal(true)
val msg = result.unwrap_err().message
expect(msg).to_contain("VHDL-KERNEL-UNSUPPORTED")
expect(msg).to_contain("gpu_syncthreads")
```

</details>

#### rejects a kernel with gpu_shared_mem (GpuSharedAlloc) fail closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_vhdl_shared_alloc_kernel()
val result = emit_vhdl_kernel_entity(func)

expect(result.is_err()).to_equal(true)
val msg = result.unwrap_err().message
expect(msg).to_contain("VHDL-KERNEL-UNSUPPORTED")
expect(msg).to_contain("gpu_shared_mem")
```

</details>

#### rejects kernel with non-unit return type fail closed

- symbol: SymbolId
- signature: MirSignature
- blocks: [empty kernel block
- entry block: BlockId entry
- span: Span empty
- vhdl metadata: vhdl hardware metadata default
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single-entry Dict avoids the struct-key Dict iteration P2 bug.
val module = make_module([make_vhdl_vector_add_kernel()])
val result = emit_vhdl_kernel_entities_for_module(module)

expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_contain("entity vhdl_vector_add_u32 is")
```

</details>

#### module emission rejects if any kernel has unsupported construct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
