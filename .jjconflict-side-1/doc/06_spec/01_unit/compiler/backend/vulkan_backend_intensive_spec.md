# Vulkan Backend Intensive Specification

> Tests covering Vulkan MIR backend intensive supported and fail-closed contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Backend Intensive Specification

## Scenarios

### Vulkan MIR backend intensive supported and fail-closed contract

#### caches struct and function type keys without duplicate emission

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- caches struct and function type keys without duplicate emission
   - Expected: builder.emit_type_struct([7, 11]) equals `struct_id`
   - Expected: builder.emit_type_function(struct_id, [7, 11]) equals `function_id`
   - Expected: builder.get_bound() equals `3`
   - Expected: builder.get_output() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("caches struct and function type keys without duplicate emission")
var builder = SpirvBuilder.create([1, 3])
val struct_id = builder.emit_type_struct([7, 11])
expect(builder.emit_type_struct([7, 11])).to_equal(struct_id)
val function_id = builder.emit_type_function(struct_id, [7, 11])
expect(builder.emit_type_function(struct_id, [7, 11])).to_equal(function_id)
expect(builder.get_bound()).to_equal(3)
expect(builder.get_output()).to_equal([
    "%1 = OpTypeStruct %7 %11",
    "%2 = OpTypeFunction %1 %7 %11"
])
```

</details>

#### emits an entry point and all GPU invocation IDs without placeholders

- emits an entry point and all GPU invocation IDs without placeholders


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits an entry point and all GPU invocation IDs without placeholders")
val instructions = [
    vulkan_inst(MirInstKind.GpuGlobalId(vulkan_local(1), 0)),
    vulkan_inst(MirInstKind.GpuLocalId(vulkan_local(2), 1)),
    vulkan_inst(MirInstKind.GpuBlockId(vulkan_local(3), 2))
]
val output = compile_supported_vulkan_with_locals(
    instructions,
    MirTerminator.Ret(nil),
    [vulkan_temp(1, vulkan_i64()), vulkan_temp(2, vulkan_i64()), vulkan_temp(3, vulkan_i64())]
)
assert_no_placeholder_output(output)
expect(output).to_contain("GlobalInvocationId")
expect(output).to_contain("LocalInvocationId")
expect(output).to_contain("WorkgroupId")
expect(output).to_contain("OpCapability Int64")
expect(output).to_contain("OpUConvert")
expect(output).to_contain("OpReturn")
```

</details>

#### lowers block and grid dimensions as typed integer values

- lowers block and grid dimensions as typed integer values


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers block and grid dimensions as typed integer values")
val output = compile_supported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuGridDim(vulkan_local(0), 2)),
        vulkan_inst(MirInstKind.GpuBlockDim(vulkan_local(1), 0)),
        vulkan_inst(MirInstKind.BinOp(vulkan_local(2), MirBinOp.Mul, vulkan_operand(0), vulkan_operand(1)))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i64()), vulkan_temp(1, vulkan_i64()), vulkan_temp(2, vulkan_i64())]
)
expect(output).to_contain("OpEntryPoint GLCompute %11 \"intensive_vulkan_kernel\" %7 %8 %9 %10")
expect(output).to_contain("OpDecorate %10 BuiltIn NumWorkgroups")
expect(output).to_contain("%10 = OpVariable %5 Input")
expect(output).to_contain("%17 = OpConstant %3 256")
expect(output).to_contain("%19 = OpLoad %4 %10")
expect(output).to_contain("%20 = OpCompositeExtract %2 %19 2")
expect(output).to_contain("%21 = OpUConvert %3 %20")
expect(output).to_contain("%22 = OpIMul %3 %21 %17")
```

</details>

#### keeps U32 block and grid dimensions on the direct value path

- keeps U32 block and grid dimensions on the direct value path
   - Expected: output does not contain `OpCapability Int64`
   - Expected: output does not contain `OpUConvert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps U32 block and grid dimensions on the direct value path")
val output = compile_supported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuGridDim(vulkan_local(0), 1)),
        vulkan_inst(MirInstKind.GpuBlockDim(vulkan_local(1), 0)),
        vulkan_inst(MirInstKind.BinOp(vulkan_local(2), MirBinOp.Add, vulkan_operand(0), vulkan_operand(1)))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_u32()), vulkan_temp(1, vulkan_u32()), vulkan_temp(2, vulkan_u32())]
)
expect(output).to_contain("%16 = OpConstant %2 256")
expect(output).to_contain("%19 = OpCompositeExtract %2 %18 1")
expect(output).to_contain("%20 = OpIAdd %2 %19 %16")
expect(output.contains("OpCapability Int64")).to_equal(false)
expect(output.contains("OpUConvert")).to_equal(false)
```

</details>

#### assembles and validates invocation IDs and a workgroup barrier when SPIR-V Tools are installed

- assembles and validates invocation IDs and a workgroup barrier when SPIR-V Tools are installed


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assembles and validates invocation IDs and a workgroup barrier when SPIR-V Tools are installed")
val output = compile_supported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuGridDim(vulkan_local(0), 0)),
        vulkan_inst(MirInstKind.GpuBlockDim(vulkan_local(3), 0)),
        vulkan_inst(MirInstKind.BinOp(vulkan_local(4), MirBinOp.Mul, vulkan_operand(0), vulkan_operand(3))),
        vulkan_inst(MirInstKind.Const(vulkan_local(1), MirConstValue.Int(-1), vulkan_i64())),
        vulkan_inst(MirInstKind.BinOp(vulkan_local(2), MirBinOp.Add, vulkan_operand(4), vulkan_operand(1))),
        vulkan_inst(MirInstKind.GpuBarrier(GpuBarrierScope.Workgroup)),
        vulkan_inst(MirInstKind.GpuMemFence(GpuMemoryScope.Workgroup)),
        vulkan_inst(MirInstKind.GpuMemFence(GpuMemoryScope.Device))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_i64()), vulkan_temp(1, vulkan_i64()), vulkan_temp(2, vulkan_i64()),
        vulkan_temp(3, vulkan_i64()), vulkan_temp(4, vulkan_i64())
    ]
)
assert_spirv_valid_if_available(output, "simple_vulkan_intensive")
```

</details>

#### rejects non-U32 constants

- rejects non-U32 constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-U32 constants")
val constant = MirInstKind.Const(vulkan_local(0), MirConstValue.Int(7), vulkan_i32())
val error = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(constant)],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i32())]
)
assert_backend_error_contains(error, "require U32")
```

</details>

#### tracks source-level I64 invocation IDs, constants, copies, moves, and arithmetic

- tracks source-level I64 invocation IDs, constants, copies, moves, and arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks source-level I64 invocation IDs, constants, copies, moves, and arithmetic")
val instructions = [
    vulkan_inst(MirInstKind.GpuGlobalId(vulkan_local(0), 0)),
    vulkan_inst(MirInstKind.Const(vulkan_local(1), MirConstValue.Int(-1), vulkan_i64())),
    vulkan_inst(MirInstKind.BinOp(vulkan_local(2), MirBinOp.Add, vulkan_operand(0), vulkan_operand(1))),
    vulkan_inst(MirInstKind.Copy(vulkan_local(3), vulkan_local(2))),
    vulkan_inst(MirInstKind.Move(vulkan_local(4), vulkan_local(3))),
    vulkan_inst(MirInstKind.BinOp(vulkan_local(5), MirBinOp.Sub, vulkan_operand(4), vulkan_operand(1))),
    vulkan_inst(MirInstKind.BinOp(vulkan_local(6), MirBinOp.Mul, vulkan_operand(5), vulkan_i64_operand(-2)))
]
val locals = [
    vulkan_temp(0, vulkan_i64()), vulkan_temp(1, vulkan_i64()),
    vulkan_temp(2, vulkan_i64()), vulkan_temp(3, vulkan_i64()),
    vulkan_temp(4, vulkan_i64()), vulkan_temp(5, vulkan_i64()),
    vulkan_temp(6, vulkan_i64())
]
val output = compile_supported_vulkan_with_locals(instructions, MirTerminator.Ret(nil), locals)
expect(output).to_contain("%16 = OpConstant %3 0xffffffffffffffff")
expect(output).to_contain("%17 = OpConstant %3 0xfffffffffffffffe")
expect(output).to_contain("%20 = OpCompositeExtract %2 %19 0")
expect(output).to_contain("%21 = OpUConvert %3 %20")
expect(output).to_contain("%22 = OpIAdd %3 %21 %16")
expect(output).to_contain("%23 = OpISub %3 %22 %16")
expect(output).to_contain("%24 = OpIMul %3 %23 %17")
```

</details>

#### does not make predeclared constants live before their MIR instruction

- does not make predeclared constants live before their MIR instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not make predeclared constants live before their MIR instruction")
val error = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.BinOp(vulkan_local(2), MirBinOp.Add, vulkan_operand(0), vulkan_operand(1))),
        vulkan_inst(MirInstKind.Const(vulkan_local(0), MirConstValue.Int(8), vulkan_i64())),
        vulkan_inst(MirInstKind.Const(vulkan_local(1), MirConstValue.Int(2), vulkan_i64()))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i64()), vulkan_temp(1, vulkan_i64()), vulkan_temp(2, vulkan_i64())]
)
assert_backend_error_contains(error, "has no value")
```

</details>

#### rejects out-of-range U32 constants

- rejects out-of-range U32 constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects out-of-range U32 constants")
val constant = MirInstKind.Const(vulkan_local(0), MirConstValue.Int(-1), vulkan_u32())
val error = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(constant)],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_u32())]
)
assert_backend_error_contains(error, "out of range")
```

</details>

#### rejects out-of-range invocation dimensions

- rejects out-of-range invocation dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects out-of-range invocation dimensions")
val error = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuGlobalId(vulkan_local(0), 3))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i64())]
)
assert_backend_error_contains(error, "dimension must be 0, 1, or 2")
```

</details>

#### rejects invalid block and grid dimensions

- rejects invalid block and grid dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects invalid block and grid dimensions")
val block_error = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuBlockDim(vulkan_local(0), 3))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_u32())]
)
assert_backend_error_contains(block_error, "block dimension must be 0, 1, or 2")

val grid_error = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuGridDim(vulkan_local(0), -1))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_u32())]
)
assert_backend_error_contains(grid_error, "grid dimension must be 0, 1, or 2")
```

</details>

#### rejects non-integer block and grid dimension destinations

- rejects non-integer block and grid dimension destinations


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-integer block and grid dimension destinations")
val block_error = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuBlockDim(vulkan_local(0), 0))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i32())]
)
assert_backend_error_contains(block_error, "block dimension destination must be U32 or I64")

val grid_error = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuGridDim(vulkan_local(0), 0))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i32())]
)
assert_backend_error_contains(grid_error, "grid dimension destination must be U32 or I64")
```

</details>

#### emits valid workgroup and subgroup control barrier constants

- emits valid workgroup and subgroup control barrier constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits valid workgroup and subgroup control barrier constants")
val workgroup = compile_supported_vulkan(
    [vulkan_inst(MirInstKind.GpuBarrier(GpuBarrierScope.Workgroup))],
    MirTerminator.Ret(nil)
)
expect(workgroup).to_contain("%10 = OpConstant %2 2")
expect(workgroup).to_contain("%13 = OpConstant %2 264")
expect(workgroup).to_contain("OpControlBarrier %10 %10 %13")

val subgroup = compile_supported_vulkan(
    [vulkan_inst(MirInstKind.GpuBarrier(GpuBarrierScope.Subgroup))],
    MirTerminator.Ret(nil)
)
expect(subgroup).to_contain("%11 = OpConstant %2 3")
expect(subgroup).to_contain("%14 = OpConstant %2 2376")
expect(subgroup).to_contain("OpControlBarrier %11 %11 %14")
```

</details>

#### emits valid workgroup and device memory barriers

- emits valid workgroup and device memory barriers


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits valid workgroup and device memory barriers")
val workgroup = compile_supported_vulkan(
    [vulkan_inst(MirInstKind.GpuMemFence(GpuMemoryScope.Workgroup))],
    MirTerminator.Ret(nil)
)
expect(workgroup).to_contain("%10 = OpConstant %2 2")
expect(workgroup).to_contain("%13 = OpConstant %2 264")
expect(workgroup).to_contain("OpMemoryBarrier %10 %13")

val device = compile_supported_vulkan(
    [vulkan_inst(MirInstKind.GpuMemFence(GpuMemoryScope.Device))],
    MirTerminator.Ret(nil)
)
expect(device).to_contain("%12 = OpConstant %2 1")
expect(device).to_contain("%14 = OpConstant %2 2376")
expect(device).to_contain("OpMemoryBarrier %12 %14")
```

</details>

#### compile_module retains a fence-only compute kernel

- compile_module retains a fence-only compute kernel
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile_module retains a fence-only compute kernel")
val fn_ = vulkan_function(
    [vulkan_inst(MirInstKind.GpuMemFence(GpuMemoryScope.Workgroup))],
    MirTerminator.Ret(nil)
)
val result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(fn_))
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().text_output).to_contain("OpMemoryBarrier %10 %13")
```

</details>

#### compile_module skips a non-kernel helper

- compile_module skips a non-kernel helper
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile_module skips a non-kernel helper")
val kernel = vulkan_function([], MirTerminator.Ret(nil))
val helper = MirFunction(
    symbol: SymbolId(id: 2), name: "cpu_helper",
    signature: MirSignature(params: [], return_type: MirType.unit(), is_variadic: false),
    locals: [], blocks: vulkan_body([], MirTerminator.Ret(nil)).blocks,
    entry_block: BlockId.entry(), span: Span.empty(),
    generic_params: [], is_generic_template: false, specialization_of: nil,
    type_bindings: {}, layout_phase: nil, is_kernel: false,
    gpu_target: "", gpu_backend_order: "", is_export_c: false,
    export_name: "", has_driver_manifest_attr: false, driver_manifest_attr: nil,
    has_vhdl_metadata: false, vhdl_metadata: vhdl_hardware_metadata_default(), has_fast_math: false
)
var functions: Dict<SymbolId, MirFunction> = {}
functions[helper.symbol] = helper
functions[kernel.symbol] = kernel
val module = MirModule(name: "vulkan_mixed", functions: functions, statics: {}, constants: {}, types: {})
val result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(module)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().text_output).to_contain("OpEntryPoint GLCompute")
```

</details>

#### rejects impossible device-wide barriers and unsupported memory scopes

- rejects impossible device-wide barriers and unsupported memory scopes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects impossible device-wide barriers and unsupported memory scopes")
val barrier_error = reject_unsupported_vulkan([vulkan_inst(MirInstKind.GpuBarrier(GpuBarrierScope.Device))], MirTerminator.Ret(nil))
assert_backend_error_contains(barrier_error, "cannot synchronize all workgroups")
val queue_error = reject_unsupported_vulkan([vulkan_inst(MirInstKind.GpuMemFence(GpuMemoryScope.QueueFamily))], MirTerminator.Ret(nil))
assert_backend_error_contains(queue_error, "requires the Vulkan memory model")
val all_error = reject_unsupported_vulkan([vulkan_inst(MirInstKind.GpuMemFence(GpuMemoryScope.All))], MirTerminator.Ret(nil))
assert_backend_error_contains(all_error, "does not support CrossDevice")
```

</details>

#### lowers indexed U32 shared memory through Workgroup pointers

- lowers indexed U32 shared memory through Workgroup pointers


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers indexed U32 shared memory through Workgroup pointers")
val output = compile_supported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 256)),
        vulkan_inst(MirInstKind.GpuLocalId(vulkan_local(1), 0)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(0), [vulkan_operand(1)])),
        vulkan_inst(MirInstKind.Const(vulkan_local(3), MirConstValue.Int(7), vulkan_u32())),
        vulkan_inst(MirInstKind.Store(vulkan_operand(2), vulkan_operand(3))),
        vulkan_inst(MirInstKind.Load(vulkan_local(4), vulkan_operand(2))),
        vulkan_inst(MirInstKind.BinOp(vulkan_local(5), MirBinOp.Add, vulkan_operand(4), vulkan_u32_operand(1)))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_u32()),
        vulkan_temp(2, vulkan_ptr_u32()), vulkan_temp(3, vulkan_u32()),
        vulkan_temp(4, vulkan_u32()), vulkan_temp(5, vulkan_u32())
    ]
)
expect(output).to_contain("OpEntryPoint GLCompute %10 \"intensive_vulkan_kernel\" %6 %7 %8 %9")
expect(output).to_contain("%16 = OpConstant %2 256")
expect(output).to_contain("%18 = OpTypePointer Workgroup %2")
expect(output).to_contain("%19 = OpTypeArray %2 %16")
expect(output).to_contain("%20 = OpTypePointer Workgroup %19")
expect(output).to_contain("%9 = OpVariable %20 Workgroup")
expect(output).to_contain("%24 = OpAccessChain %18 %9 %23")
expect(output).to_contain("OpStore %24 %17")
expect(output).to_contain("%25 = OpLoad %2 %24")
expect(output).to_contain("%26 = OpIAdd %2 %25 %13")
assert_spirv_valid_if_available(output, "simple_vulkan_shared_u32")
```

</details>

#### lowers a bounds-checked U32 storage-buffer elementwise kernel

- lowers a bounds-checked U32 storage-buffer elementwise kernel
   - Expected: output does not contain `OpLoopMerge`


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a bounds-checked U32 storage-buffer elementwise kernel")
val body = vulkan_body_with_blocks(
    [
        MirBlock(
            id: BlockId.entry(), label: Some("entry"),
            instructions: [
                vulkan_inst(MirInstKind.GpuGlobalId(vulkan_local(3), 0)),
                vulkan_inst(MirInstKind.BinOp(vulkan_local(4), MirBinOp.Lt, vulkan_operand(3), vulkan_operand(2)))
            ],
            terminator: MirTerminator.If(vulkan_operand(4), BlockId.new(1), BlockId.new(2))
        ),
        MirBlock(
            id: BlockId.new(1), label: Some("body"),
            instructions: [
                vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(5), vulkan_operand(0), [vulkan_operand(3)])),
                vulkan_inst(MirInstKind.Load(vulkan_local(7), vulkan_operand(5))),
                vulkan_inst(MirInstKind.Const(vulkan_local(8), MirConstValue.Int(2), vulkan_u32())),
                vulkan_inst(MirInstKind.BinOp(vulkan_local(9), MirBinOp.Mul, vulkan_operand(7), vulkan_operand(8))),
                vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(6), vulkan_operand(1), [vulkan_operand(3)])),
                vulkan_inst(MirInstKind.Store(vulkan_operand(6), vulkan_operand(9)))
            ],
            terminator: MirTerminator.Goto(BlockId.new(2))
        ),
        MirBlock(
            id: BlockId.new(2), label: Some("exit"),
            instructions: [],
            terminator: MirTerminator.Ret(nil)
        )
    ],
    [
        vulkan_arg(0, 0, vulkan_const_ptr_u32()),
        vulkan_arg(1, 1, vulkan_mut_ptr_u32()),
        vulkan_arg(2, 2, vulkan_u32()),
        vulkan_temp(3, vulkan_u32()), vulkan_temp(4, MirType.bool()),
        vulkan_temp(5, vulkan_const_ptr_u32()), vulkan_temp(6, vulkan_mut_ptr_u32()),
        vulkan_temp(7, vulkan_u32()), vulkan_temp(8, vulkan_u32()), vulkan_temp(9, vulkan_u32())
    ],
    3,
    MirType.unit()
)
val output = compile_supported_vulkan_body(body)
expect(output).to_contain("OpTypeRuntimeArray")
expect(output).to_contain("OpTypePointer StorageBuffer")
expect(output).to_contain("DescriptorSet 0")
expect(output).to_contain("Binding 0")
expect(output).to_contain("Binding 1")
expect(output).to_contain("OpTypeBool")
expect(output).to_contain("OpULessThan")
expect(output).to_contain("OpSelectionMerge")
expect(output).to_contain("OpBranchConditional")
expect(output).to_contain("OpAccessChain")
expect(output).to_contain("OpLoad")
expect(output).to_contain("OpIMul")
expect(output).to_contain("OpStore")
expect(output.contains("OpLoopMerge")).to_equal(false)
assert_spirv_valid_if_available(output, "simple_vulkan_storage_u32_elementwise")
```

</details>

#### accepts the empty false block emitted for source if without else

- accepts the empty false block emitted for source if without else


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts the empty false block emitted for source if without else")
val body = vulkan_body_with_blocks(
    [
        MirBlock(
            id: BlockId.entry(), label: Some("entry"), instructions: [],
            terminator: MirTerminator.If(MirOperand.const_bool(true), BlockId.new(1), BlockId.new(2))
        ),
        MirBlock(
            id: BlockId.new(1), label: Some("then"), instructions: [],
            terminator: MirTerminator.Goto(BlockId.new(3))
        ),
        MirBlock(
            id: BlockId.new(2), label: Some("else"), instructions: [],
            terminator: MirTerminator.Goto(BlockId.new(3))
        ),
        MirBlock(
            id: BlockId.new(3), label: Some("merge"), instructions: [],
            terminator: MirTerminator.Ret(nil)
        )
    ],
    [],
    0,
    MirType.unit()
)
val output = compile_supported_vulkan_body(body)
expect(output).to_contain("OpSelectionMerge")
assert_spirv_valid_if_available(output, "simple_vulkan_empty_false_block")
```

</details>

#### rejects a real else branch until general structured CFG lowering exists

- rejects a real else branch until general structured CFG lowering exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a real else branch until general structured CFG lowering exists")
val body = vulkan_body_with_blocks(
    [
        MirBlock(
            id: BlockId.entry(), label: Some("entry"), instructions: [],
            terminator: MirTerminator.If(MirOperand.const_bool(true), BlockId.new(1), BlockId.new(2))
        ),
        MirBlock(
            id: BlockId.new(1), label: Some("then"), instructions: [],
            terminator: MirTerminator.Goto(BlockId.new(3))
        ),
        MirBlock(
            id: BlockId.new(2), label: Some("else"),
            instructions: [vulkan_inst(MirInstKind.Const(vulkan_local(0), MirConstValue.Int(1), vulkan_u32()))],
            terminator: MirTerminator.Goto(BlockId.new(3))
        ),
        MirBlock(
            id: BlockId.new(3), label: Some("merge"), instructions: [],
            terminator: MirTerminator.Ret(nil)
        )
    ],
    [vulkan_temp(0, vulkan_u32())],
    0,
    MirType.unit()
)
val error = reject_unsupported_vulkan_body(body)
assert_backend_error_contains(error, "only if-without-else")
```

</details>

#### keeps multiple Vulkan shared arrays distinct and deterministic

- keeps multiple Vulkan shared arrays distinct and deterministic


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps multiple Vulkan shared arrays distinct and deterministic")
val output = compile_supported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 256)),
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(1), vulkan_u32(), 512)),
        vulkan_inst(MirInstKind.GpuLocalId(vulkan_local(6), 0)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(0), [vulkan_operand(6)])),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(3), vulkan_operand(1), [vulkan_operand(6)])),
        vulkan_inst(MirInstKind.Store(vulkan_operand(2), vulkan_u32_operand(5))),
        vulkan_inst(MirInstKind.Store(vulkan_operand(3), vulkan_u32_operand(7))),
        vulkan_inst(MirInstKind.Load(vulkan_local(4), vulkan_operand(2))),
        vulkan_inst(MirInstKind.Load(vulkan_local(5), vulkan_operand(3)))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32()),
        vulkan_temp(2, vulkan_ptr_u32()), vulkan_temp(3, vulkan_ptr_u32()),
        vulkan_temp(4, vulkan_u32()), vulkan_temp(5, vulkan_u32()),
        vulkan_temp(6, vulkan_u32())
    ]
)
expect(output).to_contain("OpEntryPoint GLCompute %11 \"intensive_vulkan_kernel\" %6 %7 %8 %9 %10")
expect(output).to_contain("%9 = OpVariable %23 Workgroup")
expect(output).to_contain("%10 = OpVariable %25 Workgroup")
expect(output).to_contain("%29 = OpAccessChain %21 %9 %28")
expect(output).to_contain("%30 = OpAccessChain %21 %10 %28")
expect(output).to_contain("OpStore %29 %19")
expect(output).to_contain("OpStore %30 %20")
expect(output).to_contain("%31 = OpLoad %2 %29")
expect(output).to_contain("%32 = OpLoad %2 %30")
assert_spirv_valid_if_available(output, "simple_vulkan_shared_multi")
```

</details>

#### supports inline I64 shared-memory indices without an I64 local

- supports inline I64 shared-memory indices without an I64 local


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports inline I64 shared-memory indices without an I64 local")
val output = compile_supported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 4)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_i64_operand(2)])),
        vulkan_inst(MirInstKind.Store(vulkan_operand(1), vulkan_u32_operand(5)))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32())]
)
expect(output).to_contain("OpCapability Int64")
expect(output).to_contain("%3 = OpTypeInt 64 0")
expect(output).to_contain("%18 = OpConstant %3 2")
expect(output).to_contain("%24 = OpAccessChain %20 %10 %18")
expect(output).to_contain("OpStore %24 %19")
assert_spirv_valid_if_available(output, "simple_vulkan_shared_i64_index")
```

</details>

#### rejects invalid Vulkan shared allocation shapes

- rejects invalid Vulkan shared allocation shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects invalid Vulkan shared allocation shapes")
val bad_type = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_i32(), 16))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32())]
)
assert_backend_error_contains(bad_type, "element type must be U32")

val bad_size = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 0))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32())]
)
assert_backend_error_contains(bad_size, "size must be between")

val bad_dest = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i64())]
)
assert_backend_error_contains(bad_dest, "destination must be a U32 pointer")

val immutable_dest = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_const_ptr_u32())]
)
assert_backend_error_contains(immutable_dest, "mutable access")

val duplicate = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 8)),
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32())]
)
assert_backend_error_contains(duplicate, "may only be declared once")
```

</details>

#### rejects invalid Vulkan shared pointer and value flow

- rejects invalid Vulkan shared pointer and value flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 123 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects invalid Vulkan shared pointer and value flow")
val use_before_alloc = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_u32_operand(0)])),
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32())]
)
assert_backend_error_contains(use_before_alloc, "base must come from a StorageBuffer argument or GpuSharedAlloc")

val bad_arity = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [
            vulkan_u32_operand(0), vulkan_u32_operand(1)
        ]))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32())]
)
assert_backend_error_contains(bad_arity, "requires exactly one index")

val bad_base = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(1), [vulkan_u32_operand(0)]))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32()),
        vulkan_temp(2, vulkan_ptr_u32())
    ]
)
assert_backend_error_contains(bad_base, "base must come from a StorageBuffer argument or GpuSharedAlloc")

val immutable_storage_gep = reject_unsupported_vulkan_body(
    vulkan_body_with_signature(
        [vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_u32_operand(0)]))],
        MirTerminator.Ret(nil),
        [vulkan_arg(0, 0, vulkan_const_ptr_u32()), vulkan_temp(1, vulkan_mut_ptr_u32())],
        1,
        MirType.unit()
    )
)
assert_backend_error_contains(immutable_storage_gep, "immutable StorageBuffer base")

val bad_index = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(0), [vulkan_operand(1)]))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_i32()),
        vulkan_temp(2, vulkan_ptr_u32())
    ]
)
assert_backend_error_contains(bad_index, "index must be U32")

val unproven_index = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(0), [vulkan_operand(1)]))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_u32()),
        vulkan_temp(2, vulkan_ptr_u32())
    ]
)
assert_backend_error_contains(unproven_index, "not proven within the allocation")

val out_of_bounds = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_u32_operand(16)]))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32())]
)
assert_backend_error_contains(out_of_bounds, "not proven within the allocation")

val stale_proof = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 256)),
        vulkan_inst(MirInstKind.GpuLocalId(vulkan_local(1), 0)),
        vulkan_inst(MirInstKind.Const(vulkan_local(1), MirConstValue.Int(256), vulkan_u32())),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(0), [vulkan_operand(1)]))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_u32()),
        vulkan_temp(2, vulkan_ptr_u32())
    ]
)
assert_backend_error_contains(stale_proof, "not proven within the allocation")

val bad_load = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_u32_operand(0)])),
        vulkan_inst(MirInstKind.Load(vulkan_local(2), vulkan_operand(1)))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32()),
        vulkan_temp(2, vulkan_i64())
    ]
)
assert_backend_error_contains(bad_load, "shared U32 element pointer and U32 destination")

val bad_store = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 16)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_u32_operand(0)])),
        vulkan_inst(MirInstKind.Store(vulkan_operand(1), vulkan_i64_operand(7)))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32())]
)
assert_backend_error_contains(bad_store, "type or range does not match")
```

</details>

#### lowers the complete U32 Workgroup atomic set with legal semantics

- lowers the complete U32 Workgroup atomic set with legal semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers the complete U32 Workgroup atomic set with legal semantics")
val output = compile_supported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 256)),
        vulkan_inst(MirInstKind.GpuLocalId(vulkan_local(1), 0)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(0), [vulkan_operand(1)])),
        vulkan_inst(MirInstKind.Store(vulkan_operand(2), vulkan_u32_operand(0))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(3), GpuAtomicOpKind.Add, vulkan_operand(2), vulkan_u32_operand(1))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(4), GpuAtomicOpKind.Sub, vulkan_operand(2), vulkan_u32_operand(2))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(5), GpuAtomicOpKind.And, vulkan_operand(2), vulkan_u32_operand(0))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(6), GpuAtomicOpKind.Or, vulkan_operand(2), vulkan_u32_operand(4))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(7), GpuAtomicOpKind.Xor, vulkan_operand(2), vulkan_u32_operand(8))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(8), GpuAtomicOpKind.Min, vulkan_operand(2), vulkan_u32_operand(3))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(9), GpuAtomicOpKind.Max, vulkan_operand(2), vulkan_u32_operand(7))),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(10), GpuAtomicOpKind.Exchange, vulkan_operand(2), vulkan_u32_operand(9))),
        vulkan_inst(MirInstKind.GpuAtomicCas(vulkan_local(11), vulkan_operand(2), vulkan_u32_operand(8), vulkan_u32_operand(6))),
        vulkan_inst(MirInstKind.BinOp(vulkan_local(12), MirBinOp.Add, vulkan_operand(3), vulkan_operand(11)))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_u32()),
        vulkan_temp(2, vulkan_ptr_u32()), vulkan_temp(3, vulkan_u32()),
        vulkan_temp(4, vulkan_u32()), vulkan_temp(5, vulkan_u32()),
        vulkan_temp(6, vulkan_u32()), vulkan_temp(7, vulkan_u32()),
        vulkan_temp(8, vulkan_u32()), vulkan_temp(9, vulkan_u32()),
        vulkan_temp(10, vulkan_u32()), vulkan_temp(11, vulkan_u32()),
        vulkan_temp(12, vulkan_u32())
    ]
)
expect(output).to_contain("%16 = OpConstant %2 258")
expect(output).to_contain("%31 = OpAtomicIAdd %2 %30 %11 %14 %13")
expect(output).to_contain("%32 = OpAtomicISub %2 %30 %11 %14 %11")
expect(output).to_contain("%33 = OpAtomicAnd %2 %30 %11 %14 %18")
expect(output).to_contain("%34 = OpAtomicOr %2 %30 %11 %14 %19")
expect(output).to_contain("%35 = OpAtomicXor %2 %30 %11 %14 %20")
expect(output).to_contain("%36 = OpAtomicUMin %2 %30 %11 %14 %12")
expect(output).to_contain("%37 = OpAtomicUMax %2 %30 %11 %14 %21")
expect(output).to_contain("%38 = OpAtomicExchange %2 %30 %11 %14 %22")
expect(output).to_contain("%39 = OpAtomicCompareExchange %2 %30 %11 %14 %16 %23 %20")
expect(output).to_contain("%40 = OpIAdd %2 %31 %39")
assert_spirv_valid_if_available(output, "simple_vulkan_shared_atomics")
```

</details>

#### rejects malformed Vulkan shared atomics

- rejects malformed Vulkan shared atomics


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects malformed Vulkan shared atomics")
val generic_cas = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 1)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_u32_operand(0)])),
        vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(2), GpuAtomicOpKind.CompareExchange, vulkan_operand(1), vulkan_u32_operand(1)))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32()),
        vulkan_temp(2, vulkan_u32())
    ]
)
assert_backend_error_contains(generic_cas, "requires GpuAtomicCas")

val bad_pointer = reject_unsupported_vulkan_with_locals(
    [vulkan_inst(MirInstKind.GpuAtomicOp(vulkan_local(1), GpuAtomicOpKind.Add, vulkan_operand(0), vulkan_u32_operand(1)))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_u32())]
)
assert_backend_error_contains(bad_pointer, "lowered shared U32 pointer")

val bad_dest = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.GpuSharedAlloc(vulkan_local(0), vulkan_u32(), 1)),
        vulkan_inst(MirInstKind.GetElementPtr(vulkan_local(1), vulkan_operand(0), [vulkan_u32_operand(0)])),
        vulkan_inst(MirInstKind.GpuAtomicCas(vulkan_local(2), vulkan_operand(1), vulkan_u32_operand(0), vulkan_u32_operand(1)))
    ],
    MirTerminator.Ret(nil),
    [
        vulkan_temp(0, vulkan_ptr_u32()), vulkan_temp(1, vulkan_ptr_u32()),
        vulkan_temp(2, vulkan_i64())
    ]
)
assert_backend_error_contains(bad_dest, "U32 pointer and U32 destination")
```

</details>

#### rejects non-unit parameterized and value-returning Vulkan entry points

- rejects non-unit parameterized and value-returning Vulkan entry points
   - Expected: non_unit.is_err() is true
   - Expected: parameterized.is_ok() is true
   - Expected: value_return.is_err() is true
   - Expected: hidden_arg.is_err() is true
   - Expected: negative_arg_count.is_err() is true
   - Expected: oversized_arg_count.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-unit parameterized and value-returning Vulkan entry points")
val backend = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options())

val non_unit_body = vulkan_body_with_signature([], MirTerminator.Ret(nil), [], 0, vulkan_u32())
val non_unit = backend.compile_kernel("non_unit_vulkan", non_unit_body)
expect(non_unit.is_err()).to_equal(true)
assert_backend_error_contains(non_unit.unwrap_err(), "must return Unit")

val parameter_body = vulkan_body_with_signature(
    [], MirTerminator.Ret(nil), [vulkan_arg(0, 0, vulkan_u32())], 1, MirType.unit()
)
val parameterized = backend.compile_kernel("parameterized_vulkan", parameter_body)
expect(parameterized.is_ok()).to_equal(true)
expect(parameterized.unwrap()).to_contain("PushConstant")

val value_body = vulkan_body_with_signature(
    [], MirTerminator.Ret(Some(vulkan_u32_operand(1))), [], 0, MirType.unit()
)
val value_return = backend.compile_kernel("value_return_vulkan", value_body)
expect(value_return.is_err()).to_equal(true)
assert_backend_error_contains(value_return.unwrap_err(), "cannot return a value")

val hidden_arg = backend.compile_kernel(
    "hidden_arg_vulkan",
    vulkan_body_with_signature([], MirTerminator.Ret(nil), [vulkan_arg(0, 0, vulkan_u32())], 0, MirType.unit())
)
expect(hidden_arg.is_err()).to_equal(true)
assert_backend_error_contains(hidden_arg.unwrap_err(), "argument local index is outside its signature")

val negative_arg_count = backend.compile_kernel(
    "negative_arg_count_vulkan",
    vulkan_body_with_signature([], MirTerminator.Ret(nil), [], -1, MirType.unit())
)
expect(negative_arg_count.is_err()).to_equal(true)
assert_backend_error_contains(negative_arg_count.unwrap_err(), "argument count cannot be negative")

val oversized_arg_count = backend.compile_kernel(
    "oversized_arg_count_vulkan",
    vulkan_body_with_signature([], MirTerminator.Ret(nil), [], 1, MirType.unit())
)
expect(oversized_arg_count.is_err()).to_equal(true)
assert_backend_error_contains(oversized_arg_count.unwrap_err(), "argument local is missing from its signature")
```

</details>

#### rejects non-unit returns through compile_module

- rejects non-unit returns through compile_module
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-unit returns through compile_module")
val fn_ = vulkan_function_with_signature(
    [vulkan_inst(MirInstKind.GpuGlobalId(vulkan_local(0), 0))],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i64())],
    [],
    vulkan_u32()
)
val result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(fn_))
expect(result.is_err()).to_equal(true)
assert_backend_error_contains(result.unwrap_err(), "must return Unit")
```

</details>

#### rejects malformed Vulkan signature and argument-local bijections

- rejects malformed Vulkan signature and argument-local bijections
   - Expected: missing.is_err() is true
   - Expected: duplicate.is_err() is true
   - Expected: negative.is_err() is true
   - Expected: out_of_range.is_err() is true
   - Expected: mismatch.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects malformed Vulkan signature and argument-local bijections")
val backend = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options())
val param = [vulkan_u32()]

val missing = backend.compile_module(vulkan_module(vulkan_function_with_signature(
    [], MirTerminator.Ret(nil), [], param, MirType.unit()
)))
expect(missing.is_err()).to_equal(true)
assert_backend_error_contains(missing.unwrap_err(), "argument local is missing")

val duplicate = backend.compile_module(vulkan_module(vulkan_function_with_signature(
    [], MirTerminator.Ret(nil), [vulkan_arg(0, 0, vulkan_u32()), vulkan_arg(1, 0, vulkan_u32())], param, MirType.unit()
)))
expect(duplicate.is_err()).to_equal(true)
assert_backend_error_contains(duplicate.unwrap_err(), "argument local index is duplicated")

val negative = backend.compile_module(vulkan_module(vulkan_function_with_signature(
    [], MirTerminator.Ret(nil), [vulkan_arg(0, -1, vulkan_u32())], param, MirType.unit()
)))
expect(negative.is_err()).to_equal(true)
assert_backend_error_contains(negative.unwrap_err(), "index cannot be negative")

val out_of_range = backend.compile_module(vulkan_module(vulkan_function_with_signature(
    [], MirTerminator.Ret(nil), [vulkan_arg(0, 1, vulkan_u32())], param, MirType.unit()
)))
expect(out_of_range.is_err()).to_equal(true)
assert_backend_error_contains(out_of_range.unwrap_err(), "index is outside")

val mismatch = backend.compile_module(vulkan_module(vulkan_function_with_signature(
    [], MirTerminator.Ret(nil), [vulkan_arg(0, 0, vulkan_i32())], param, MirType.unit()
)))
expect(mismatch.is_err()).to_equal(true)
assert_backend_error_contains(mismatch.unwrap_err(), "type does not match")
```

</details>

#### assigns storage bindings by argument index when locals are reordered

- assigns storage bindings by argument index when locals are reordered
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns storage bindings by argument index when locals are reordered")
val fn_ = vulkan_function_with_signature(
    [],
    MirTerminator.Ret(nil),
    [vulkan_arg(1, 1, vulkan_ptr_u32()), vulkan_arg(0, 0, vulkan_ptr_u32())],
    [vulkan_ptr_u32(), vulkan_ptr_u32()],
    MirType.unit()
)
val result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(fn_))
expect(result.is_ok()).to_equal(true)
val output = result.unwrap().text_output
val binding_one = output.find("Binding 1")
val binding_zero = output.find("Binding 0")
expect(binding_one).to_be_greater_than(0)
expect(binding_zero).to_be_greater_than(0)
expect(binding_one).to_be_less_than(binding_zero)
```

</details>

#### selects annotated Vulkan kernels before ABI validation

- selects annotated Vulkan kernels before ABI validation
   - Expected: valid_result.is_ok() is true
   - Expected: invalid_result.is_err() is true
   - Expected: parameter_result.is_ok() is true
   - Expected: variadic_result.is_err() is true
   - Expected: return_local_result.is_err() is true
   - Expected: cuda_result.is_ok() is true
   - Expected: cuda_result.unwrap().text_output does not contain `OpEntryPoint GLCompute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects annotated Vulkan kernels before ABI validation")
val valid = vulkan_function([], MirTerminator.Ret(nil))
val valid_result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(valid))
expect(valid_result.is_ok()).to_equal(true)
expect(valid_result.unwrap().text_output).to_contain("OpEntryPoint GLCompute")

val invalid = vulkan_function_with_signature([], MirTerminator.Ret(nil), [], [], vulkan_u32())
val invalid_result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(invalid))
expect(invalid_result.is_err()).to_equal(true)
assert_backend_error_contains(invalid_result.unwrap_err(), "must return Unit")

val parameterized = vulkan_function_with_signature(
    [], MirTerminator.Ret(nil), [vulkan_arg(0, 0, vulkan_u32())], [vulkan_u32()], MirType.unit()
)
val parameter_result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(parameterized))
expect(parameter_result.is_ok()).to_equal(true)
expect(parameter_result.unwrap().text_output).to_contain("PushConstant")

val variadic = vulkan_function_with_abi([], MirTerminator.Ret(nil), [], [], MirType.unit(), true, "vulkan", "vulkan")
val variadic_result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(variadic))
expect(variadic_result.is_err()).to_equal(true)
assert_backend_error_contains(variadic_result.unwrap_err(), "cannot be variadic")

val return_local = vulkan_function_with_signature(
    [], MirTerminator.Ret(nil), [vulkan_return(0, MirType.unit())], [], MirType.unit()
)
val return_local_result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(return_local))
expect(return_local_result.is_err()).to_equal(true)
assert_backend_error_contains(return_local_result.unwrap_err(), "cannot have a return local")

val cuda = vulkan_function_with_abi([], MirTerminator.Ret(nil), [], [], MirType.unit(), false, "cuda", "cuda")
val cuda_result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(cuda))
expect(cuda_result.is_ok()).to_equal(true)
expect(cuda_result.unwrap().text_output.contains("OpEntryPoint GLCompute")).to_equal(false)
```

</details>

#### propagates typed instruction errors through compile_module

- propagates typed instruction errors through compile_module
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("propagates typed instruction errors through compile_module")
val bad = vulkan_function_with_locals(
    [
        vulkan_inst(MirInstKind.GpuGlobalId(vulkan_local(0), 0)),
        vulkan_inst(MirInstKind.Load(vulkan_local(1), vulkan_operand(0)))
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_i64()), vulkan_temp(1, vulkan_u32())]
)
val result = VulkanCodegenBackend.create_with_options([1, 3], compileoptions_default_options()).compile_module(vulkan_module(bad))
expect(result.is_err()).to_equal(true)
assert_backend_error_contains(result.unwrap_err(), "lowered U32 storage pointer")
```

</details>

#### rejects if and branch control flow with a typed Vulkan backend error

- rejects if and branch control flow with a typed Vulkan backend error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects if and branch control flow with a typed Vulkan backend error")
val error = reject_unsupported_vulkan(
    [vulkan_inst(MirInstKind.GpuBarrier(GpuBarrierScope.Workgroup))],
    MirTerminator.If(MirOperand.const_bool(true), BlockId.new(1), BlockId.new(2))
)
assert_backend_error_contains(error, "branch target does not exist")
```

</details>

<details>
<summary>Advanced: rejects loop and goto control flow with a typed Vulkan backend error</summary>

#### rejects loop and goto control flow with a typed Vulkan backend error

- rejects loop and goto control flow with a typed Vulkan backend error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects loop and goto control flow with a typed Vulkan backend error")
val error = reject_unsupported_vulkan(
    [vulkan_inst(MirInstKind.GpuBarrier(GpuBarrierScope.Workgroup))],
    MirTerminator.Goto(BlockId.entry())
)
assert_backend_error_contains(error, "loop back-edges")
```

</details>


</details>

#### rejects direct calls instead of emitting a successful placeholder

- rejects direct calls instead of emitting a successful placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects direct calls instead of emitting a successful placeholder")
val call = MirInstKind.Call(nil, MirOperand.const_int(1), [])
val error = reject_unsupported_vulkan([vulkan_inst(call)], MirTerminator.Ret(nil))
assert_backend_error_contains(error, "does not support instruction")
```

</details>

#### rejects unsupported U32 arithmetic

- rejects unsupported U32 arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unsupported U32 arithmetic")
val div = MirInstKind.BinOp(vulkan_local(2), MirBinOp.Div, vulkan_operand(0), vulkan_operand(1))
val error = reject_unsupported_vulkan_with_locals(
    [
        vulkan_inst(MirInstKind.Const(vulkan_local(0), MirConstValue.Int(8), vulkan_u32())),
        vulkan_inst(MirInstKind.Const(vulkan_local(1), MirConstValue.Int(2), vulkan_u32())),
        vulkan_inst(div)
    ],
    MirTerminator.Ret(nil),
    [vulkan_temp(0, vulkan_u32()), vulkan_temp(1, vulkan_u32()), vulkan_temp(2, vulkan_u32())]
)
assert_backend_error_contains(error, "integer binary operation")
```

</details>

#### rejects unary arithmetic instead of comment-only SPIR-V

- rejects unary arithmetic instead of comment-only SPIR-V


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unary arithmetic instead of comment-only SPIR-V")
val neg = MirInstKind.UnaryOp(vulkan_local(1), MirUnaryOp.Neg, vulkan_operand(0))
val error = reject_unsupported_vulkan([vulkan_inst(neg)], MirTerminator.Ret(nil))
assert_backend_error_contains(error, "unary operation lowering")
```

</details>

#### rejects host or device loads until pointer lowering is implemented

- rejects host or device loads until pointer lowering is implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects host or device loads until pointer lowering is implemented")
val load = MirInstKind.Load(vulkan_local(1), vulkan_operand(0))
val error = reject_unsupported_vulkan([vulkan_inst(load)], MirTerminator.Ret(nil))
assert_backend_error_contains(error, "lowered U32 storage pointer")
```

</details>

#### rejects host or device stores until pointer lowering is implemented

- rejects host or device stores until pointer lowering is implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects host or device stores until pointer lowering is implemented")
val store = MirInstKind.Store(vulkan_operand(0), vulkan_operand(1))
val error = reject_unsupported_vulkan([vulkan_inst(store)], MirTerminator.Ret(nil))
assert_backend_error_contains(error, "lowered U32 storage pointer")
```

</details>

#### rejects GEPs that do not use lowered storage or shared-memory pointers

- rejects GEPs that do not use lowered storage or shared-memory pointers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects GEPs that do not use lowered storage or shared-memory pointers")
val unsupported = MirInstKind.GetElementPtr(vulkan_local(2), vulkan_operand(0), [vulkan_operand(1)])
val error = reject_unsupported_vulkan([vulkan_inst(unsupported)], MirTerminator.Ret(nil))
assert_backend_error_contains(error, "storage GEP destination must be a U32 pointer")
```

</details>

#### rejects unsupported call terminators with a typed Vulkan backend error

- rejects unsupported call terminators with a typed Vulkan backend error


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unsupported call terminators with a typed Vulkan backend error")
val term = MirTerminator.CallTerminator(
    nil,
    MirOperand.const_int(1),
    [],
    BlockId.new(1),
    nil
)
val error = reject_unsupported_vulkan([], term)
assert_backend_error_contains(error, "does not support terminator")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan MIR backend intensive supported and fail-closed contract.
- Vulkan MIR backend intensive supported and fail-closed contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
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

- Canonical SPipe generation for source `44c7077637545d6f67c6b3cf85f6bfac0c69db49f2fc401f9b42b8a317981d60`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44c7077637545d6f67c6b3cf85f6bfac0c69db49f2fc401f9b42b8a317981d60`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44c7077637545d6f67c6b3cf85f6bfac0c69db49f2fc401f9b42b8a317981d60`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vulkan_backend_intensive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/vulkan_backend_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/vulkan_backend_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches struct and function type keys without duplicate emission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits an entry point and all GPU invocation IDs without placeholders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers block and grid dimensions as typed integer values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
