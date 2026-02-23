# GPU PTX Code Generation Specification
*Source:* `test/feature/usage/gpu_ptx_gen_spec.spl`
**Feature IDs:** #816-820  |  **Category:** Compiler Backend  |  **Status:** In Progress

## Overview




## Overview

PTX code generation tests verify that the CUDA backend correctly translates
MIR instructions to NVIDIA PTX assembly. These tests do NOT require GPU
hardware - they only verify the text output of the code generator.

## Key Concepts

| Concept | Description |
|---------|-------------|
| PTX | NVIDIA Parallel Thread Execution virtual ISA |
| MIR | Mid-level Intermediate Representation |
| Kernel | GPU entry point function (.entry) |
| Device Function | GPU-callable function (.func) |

## Behavior

- CudaBackend compiles MIR modules to PTX text
- PTX header contains version, target, and address size
- Kernel functions use .visible .entry directive
- Device functions use .visible .func directive
- Thread IDs accessed via special registers %tid, %ctaid, %ntid
- Barrier synchronization via bar.sync

## Feature: PTX Builder - Module Header

## PTX Module Header Generation

    Tests that PTX module headers contain correct version and target info.

### Scenario: with SM 8.6 compute capability

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct PTX header | pass |

**Example:** generates correct PTX header
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".version 7.8")
    Then  expect(ptx).to_contain(".target sm_86")
    Then  expect(ptx).to_contain(".address_size 64")
    Then  expect(ptx).to_contain("test_module")

### Scenario: with SM 7.0 compute capability

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct target for Volta | pass |

**Example:** generates correct target for Volta
    Given var builder = PtxBuilder__create((7, 0))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".target sm_70")

## Feature: PTX Builder - Register Declarations

## Register Declaration Generation

    Tests PTX register declarations for various types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | declares integer registers | pass |
| 2 | declares float registers | pass |
| 3 | declares predicate registers | pass |
| 4 | declares unsigned integer registers | pass |

**Example:** declares integer registers
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".reg .s64 %r0;")

**Example:** declares float registers
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".reg .f32 %f0;")

**Example:** declares predicate registers
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".reg .pred %p0;")

**Example:** declares unsigned integer registers
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".reg .u32 %u0;")

## Feature: PTX Builder - Arithmetic Operations

## Arithmetic Instruction Generation

    Tests PTX arithmetic instruction emission.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates integer add | pass |
| 2 | generates integer subtract | pass |
| 3 | generates integer multiply with low-word | pass |
| 4 | generates float multiply | pass |
| 5 | generates float divide with rounding | pass |
| 6 | generates approximate float divide for f32 | pass |
| 7 | generates negate | pass |

**Example:** generates integer add
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("add.s64 %r0, %r1, %r2;")

**Example:** generates integer subtract
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("sub.s32 %r0, %r1, %r2;")

**Example:** generates integer multiply with low-word
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mul.lo.s64 %r0, %r1, %r2;")

**Example:** generates float multiply
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mul.f32 %f0, %f1, %f2;")

**Example:** generates float divide with rounding
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("div.rn.f64 %f0, %f1, %f2;")

**Example:** generates approximate float divide for f32
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("div.approx.f32 %f0, %f1, %f2;")

**Example:** generates negate
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("neg.s64 %r0, %r1;")

## Feature: PTX Builder - Comparisons

## Comparison and Predicate Generation

    Tests set-predicate instruction generation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates equality comparison | pass |
| 2 | generates less-than comparison | pass |

**Example:** generates equality comparison
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("setp.eq.s64 %p0, %r0, %r1;")

**Example:** generates less-than comparison
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("setp.lt.f32 %p0, %f0, %f1;")

## Feature: PTX Builder - Memory Operations

## Memory Load/Store Generation

    Tests global, shared, and local memory access instructions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates global memory load | pass |
| 2 | generates global memory store | pass |
| 3 | generates shared memory load | pass |
| 4 | generates shared memory allocation | pass |
| 5 | generates local memory allocation | pass |

**Example:** generates global memory load
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("ld.global.s64 %r0, [%addr];")

**Example:** generates global memory store
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("st.global.s64 [%addr], %r0;")

**Example:** generates shared memory load
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("ld.shared.f32 %r0, [%saddr];")

**Example:** generates shared memory allocation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".shared .f32 shared_buf[256];")

**Example:** generates local memory allocation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain(".local .s64 local_buf[8];")

## Feature: PTX Builder - Thread IDs

## Thread and Block ID Access

    Tests special register access for thread identification.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates thread ID access for x dimension | pass |
| 2 | generates thread ID access for y dimension | pass |
| 3 | generates block ID access | pass |
| 4 | generates block dim access | pass |
| 5 | generates grid dim access | pass |
| 6 | computes global thread ID | pass |

**Example:** generates thread ID access for x dimension
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mov.u32 %tid_x, %tid.x;")

**Example:** generates thread ID access for y dimension
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mov.u32 %tid_y, %tid.y;")

**Example:** generates block ID access
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mov.u32 %bid_x, %ctaid.x;")

**Example:** generates block dim access
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mov.u32 %bdim_x, %ntid.x;")

**Example:** generates grid dim access
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mov.u32 %gdim_x, %nctaid.x;")

**Example:** computes global thread ID
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mul.lo.u32")
    Then  expect(ptx).to_contain("add.u32")

## Feature: PTX Builder - Synchronization

## Barrier and Memory Fence Generation

    Tests synchronization instruction generation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates block-level barrier | pass |
| 2 | generates CTA memory barrier | pass |
| 3 | generates global memory barrier | pass |
| 4 | generates system memory barrier | pass |

**Example:** generates block-level barrier
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("bar.sync 0;")

**Example:** generates CTA memory barrier
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("membar.cta;")

**Example:** generates global memory barrier
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("membar.gl;")

**Example:** generates system memory barrier
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("membar.sys;")

## Feature: PTX Builder - Atomic Operations

## Atomic Operation Generation

    Tests atomic instruction generation for global memory.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates atomic add | pass |
| 2 | generates atomic min | pass |
| 3 | generates atomic max | pass |
| 4 | generates atomic compare-and-swap | pass |
| 5 | generates shared memory atomic add | pass |

**Example:** generates atomic add
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("atom.global.add.s64 %r0, [%addr], %val;")

**Example:** generates atomic min
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("atom.global.min.s32 %r0, [%addr], %val;")

**Example:** generates atomic max
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("atom.global.max.u64 %r0, [%addr], %val;")

**Example:** generates atomic compare-and-swap
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("atom.global.cas.s64 %r0, [%addr], %cmp, %val;")

**Example:** generates shared memory atomic add
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("atom.shared.add.s32 %r0, [%saddr], %val;")

## Feature: PTX Builder - Type Conversions

## Type Conversion (cvt) Instruction Generation

    Tests PTX type conversion instruction emission.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | converts int to float | pass |
| 2 | converts float to int | pass |
| 3 | converts float to float | pass |
| 4 | converts int to int | pass |

**Example:** converts int to float
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("cvt.rn.f32.s32 %f0, %r0;")

**Example:** converts float to int
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("cvt.rzi.s64.f64 %r0, %f0;")

**Example:** converts float to float
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("cvt.rn.f64.f32 %f0, %f1;")

**Example:** converts int to int
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("cvt.s64.s32 %r0, %r1;")

## Feature: PTX Builder - Math Intrinsics

## Math Intrinsic Generation

    Tests PTX special function unit (SFU) instruction emission.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates sin approximation | pass |
| 2 | generates cos approximation | pass |
| 3 | generates sqrt approximation | pass |
| 4 | generates abs | pass |
| 5 | generates fused multiply-add | pass |
| 6 | generates exp2 approximation | pass |
| 7 | generates log2 approximation | pass |
| 8 | generates reciprocal approximation | pass |
| 9 | generates min instruction | pass |
| 10 | generates max instruction | pass |

**Example:** generates sin approximation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("sin.approx.f32 %f0, %f1;")

**Example:** generates cos approximation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("cos.approx.f32 %f0, %f1;")

**Example:** generates sqrt approximation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("sqrt.approx.f32 %f0, %f1;")

**Example:** generates abs
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("abs.f32 %f0, %f1;")

**Example:** generates fused multiply-add
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("fma.rn.f32 %f0, %f1, %f2, %f3;")

**Example:** generates exp2 approximation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("ex2.approx.f32 %f0, %f1;")

**Example:** generates log2 approximation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("lg2.approx.f32 %f0, %f1;")

**Example:** generates reciprocal approximation
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("rcp.approx.f32 %f0, %f1;")

**Example:** generates min instruction
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("min.f32 %f0, %f1, %f2;")

**Example:** generates max instruction
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("max.f32 %f0, %f1, %f2;")

## Feature: PTX Builder - Control Flow

## Branch and Label Generation

    Tests control flow instruction generation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates unconditional branch | pass |
| 2 | generates conditional branch | pass |
| 3 | generates negated conditional branch | pass |
| 4 | generates labels | pass |
| 5 | generates return instruction | pass |
| 6 | generates exit instruction | pass |

**Example:** generates unconditional branch
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("bra BB1;")

**Example:** generates conditional branch
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("@%p0 bra BB_true;")

**Example:** generates negated conditional branch
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("@!%p0 bra BB_false;")

**Example:** generates labels
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("BB0:")

**Example:** generates return instruction
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("ret;")

**Example:** generates exit instruction
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("exit;")

## Feature: PTX Builder - Function Calls

## Device Function Call Generation

    Tests call instruction generation for device functions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates function call with return value | pass |
| 2 | generates void function call | pass |

**Example:** generates function call with return value
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("call (%r0), device_func, (%r1, %r2);")

**Example:** generates void function call
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("call void_func, (%r0);")

## Feature: CUDA Type Mapper - Primitive Types

## Type Mapping Verification

    Tests CUDA type mapper for correct PTX type strings.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | maps integer types to PTX | pass |
| 2 | maps unsigned integer types to PTX | pass |
| 3 | maps float types to PTX | pass |
| 4 | maps bool to predicate | pass |

**Example:** maps integer types to PTX
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_type(PrimitiveType.I64)).to_equal(".s64")
    Then  expect(mapper.ptx_type(PrimitiveType.I32)).to_equal(".s32")
    Then  expect(mapper.ptx_type(PrimitiveType.I16)).to_equal(".s16")
    Then  expect(mapper.ptx_type(PrimitiveType.I8)).to_equal(".s8")

**Example:** maps unsigned integer types to PTX
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_type(PrimitiveType.U64)).to_equal(".u64")
    Then  expect(mapper.ptx_type(PrimitiveType.U32)).to_equal(".u32")
    Then  expect(mapper.ptx_type(PrimitiveType.U16)).to_equal(".u16")
    Then  expect(mapper.ptx_type(PrimitiveType.U8)).to_equal(".u8")

**Example:** maps float types to PTX
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_type(PrimitiveType.F64)).to_equal(".f64")
    Then  expect(mapper.ptx_type(PrimitiveType.F32)).to_equal(".f32")
    Then  expect(mapper.ptx_type(PrimitiveType.F16)).to_equal(".f16")

**Example:** maps bool to predicate
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_type(PrimitiveType.Bool)).to_equal(".pred")

## Feature: CUDA Type Mapper - Compute Capabilities

## Compute Capability Feature Detection

    Tests feature detection based on GPU compute capability.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | detects half precision support | pass |
| 2 | detects tensor core support | pass |
| 3 | reports correct max threads per block | pass |
| 4 | reports correct warp size | pass |
| 5 | reports correct shared memory for Ampere | pass |
| 6 | reports correct shared memory for Volta | pass |

**Example:** detects half precision support
    Given val mapper_old = CudaTypeMapper__create_sm(5, 0)
    Given val mapper_new = CudaTypeMapper__create_sm(7, 0)
    Then  expect(mapper_old.supports_half_precision()).to_equal(false)
    Then  expect(mapper_new.supports_half_precision()).to_equal(true)

**Example:** detects tensor core support
    Given val mapper_old = CudaTypeMapper__create_sm(6, 1)
    Given val mapper_new = CudaTypeMapper__create_sm(7, 0)
    Then  expect(mapper_old.supports_tensor_cores()).to_equal(false)
    Then  expect(mapper_new.supports_tensor_cores()).to_equal(true)

**Example:** reports correct max threads per block
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.max_threads_per_block()).to_equal(1024)

**Example:** reports correct warp size
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.warp_size()).to_equal(32)

**Example:** reports correct shared memory for Ampere
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.max_shared_memory()).to_equal(163840)

**Example:** reports correct shared memory for Volta
    Given val mapper = CudaTypeMapper__create_sm(7, 0)
    Given val shared_mem = mapper.max_shared_memory()
    Then  expect(shared_mem).to_equal(96 * 1024)

## Feature: CUDA Type Mapper - Memory Spaces

## Memory Space Mapping

    Tests PTX state space mapping.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | maps global memory space | pass |
| 2 | maps shared memory space | pass |
| 3 | maps local memory space | pass |
| 4 | maps constant memory space | pass |

**Example:** maps global memory space
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_state_space(MemorySpace.Global)).to_equal(".global")

**Example:** maps shared memory space
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_state_space(MemorySpace.Shared)).to_equal(".shared")

**Example:** maps local memory space
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_state_space(MemorySpace.Local)).to_equal(".local")

**Example:** maps constant memory space
    Given val mapper = CudaTypeMapper__create_sm(8, 6)
    Then  expect(mapper.ptx_state_space(MemorySpace.Constant)).to_equal(".const")

## Feature: Launch Configuration

## Kernel Launch Configuration

    Tests launch configuration validation and computation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates 1D launch config | pass |
| 2 | rounds up grid size for non-divisible total | pass |
| 3 | creates 2D launch config | pass |
| 4 | computes total blocks | pass |
| 5 | computes threads per block | pass |
| 6 | validates valid config | pass |
| 7 | rejects zero block size | pass |
| 8 | adds shared memory to config | pass |

**Example:** creates 1D launch config
    Given val config = LaunchConfig__for_1d(1024, 256)
    Then  expect(config.grid_x).to_equal(4)
    Then  expect(config.grid_y).to_equal(1)
    Then  expect(config.grid_z).to_equal(1)
    Then  expect(config.block_x).to_equal(256)
    Then  expect(config.total_threads()).to_equal(1024)

**Example:** rounds up grid size for non-divisible total
    Given val config = LaunchConfig__for_1d(1000, 256)
    Then  expect(config.grid_x).to_equal(4)
    Then  expect(config.total_threads()).to_be_greater_than(999)

**Example:** creates 2D launch config
    Given val config = LaunchConfig__for_2d(512, 512, 16, 16)
    Then  expect(config.grid_x).to_equal(32)
    Then  expect(config.grid_y).to_equal(32)
    Then  expect(config.block_x).to_equal(16)
    Then  expect(config.block_y).to_equal(16)

**Example:** computes total blocks
    Given val config = LaunchConfig__for_2d(512, 512, 16, 16)
    Then  expect(config.total_blocks()).to_equal(1024)

**Example:** computes threads per block
    Given val config = LaunchConfig__for_2d(512, 512, 16, 16)
    Then  expect(config.threads_per_block()).to_equal(256)

**Example:** validates valid config
    Given val config = LaunchConfig__for_1d(1024, 256)
    Given val err = config.validate()
    Then  expect(err).to_be_nil()

**Example:** rejects zero block size
    Given val config = LaunchConfig__for_1d(1024, 0)
    Given val err = config.validate()
    Then  expect(err).to_be_nil()  # for_1d with 0 produces invalid config

**Example:** adds shared memory to config
    Given val config = LaunchConfig__for_1d(1024, 256).with_shared_mem(4096)
    Then  expect(config.shared_mem_bytes).to_equal(4096)
    Then  expect(config.block_x).to_equal(256)

## Feature: PTX Builder - Constants

## Constant Loading

    Tests constant value loading instructions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | loads integer constant | pass |
| 2 | loads unsigned integer constant | pass |

**Example:** loads integer constant
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mov.s64 %r0, 42;")

**Example:** loads unsigned integer constant
    Given var builder = PtxBuilder__create((8, 6))
    Given val ptx = builder.build()
    Then  expect(ptx).to_contain("mov.u32 %r0, 100;")


