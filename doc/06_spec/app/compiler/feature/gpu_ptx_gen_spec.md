# GPU PTX Code Generation Specification

**Feature ID:** #816-820 | **Category:** Compiler Backend | **Difficulty:** 4/5 | **Status:** In Progress

_Source: `test/feature/usage/gpu_ptx_gen_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 81 |

## Test Structure

### PTX Builder - Module Header

#### with SM 8.6 compute capability

- ✅ generates correct PTX header
#### with SM 7.0 compute capability

- ✅ generates correct target for Volta
### PTX Builder - Register Declarations

- ✅ declares integer registers
- ✅ declares float registers
- ✅ declares predicate registers
- ✅ declares unsigned integer registers
### PTX Builder - Arithmetic Operations

- ✅ generates integer add
- ✅ generates integer subtract
- ✅ generates integer multiply with low-word
- ✅ generates float multiply
- ✅ generates float divide with rounding
- ✅ generates approximate float divide for f32
- ✅ generates negate
### PTX Builder - Comparisons

- ✅ generates equality comparison
- ✅ generates less-than comparison
### PTX Builder - Memory Operations

- ✅ generates global memory load
- ✅ generates global memory store
- ✅ generates shared memory load
- ✅ generates shared memory allocation
- ✅ generates local memory allocation
### PTX Builder - Thread IDs

- ✅ generates thread ID access for x dimension
- ✅ generates thread ID access for y dimension
- ✅ generates block ID access
- ✅ generates block dim access
- ✅ generates grid dim access
- ✅ computes global thread ID
### PTX Builder - Synchronization

- ✅ generates block-level barrier
- ✅ generates CTA memory barrier
- ✅ generates global memory barrier
- ✅ generates system memory barrier
### PTX Builder - Atomic Operations

- ✅ generates atomic add
- ✅ generates atomic min
- ✅ generates atomic max
- ✅ generates atomic compare-and-swap
- ✅ generates shared memory atomic add
### PTX Builder - Type Conversions

- ✅ converts int to float
- ✅ converts float to int
- ✅ converts float to float
- ✅ converts int to int
### PTX Builder - Math Intrinsics

- ✅ generates sin approximation
- ✅ generates cos approximation
- ✅ generates sqrt approximation
- ✅ generates abs
- ✅ generates fused multiply-add
- ✅ generates exp2 approximation
- ✅ generates log2 approximation
- ✅ generates reciprocal approximation
- ✅ generates min instruction
- ✅ generates max instruction
### PTX Builder - Control Flow

- ✅ generates unconditional branch
- ✅ generates conditional branch
- ✅ generates negated conditional branch
- ✅ generates labels
- ✅ generates return instruction
- ✅ generates exit instruction
### PTX Builder - Function Calls

- ✅ generates function call with return value
- ✅ generates void function call
### CUDA Type Mapper - Primitive Types

- ✅ maps integer types to PTX
- ✅ maps unsigned integer types to PTX
- ✅ maps float types to PTX
- ✅ maps bool to predicate
### CUDA Type Mapper - Compute Capabilities

- ✅ detects half precision support
- ✅ detects tensor core support
- ✅ reports correct max threads per block
- ✅ reports correct warp size
- ✅ reports correct shared memory for Ampere
- ✅ reports correct shared memory for Volta
### CUDA Type Mapper - Memory Spaces

- ✅ maps global memory space
- ✅ maps shared memory space
- ✅ maps local memory space
- ✅ maps constant memory space
### Launch Configuration

- ✅ creates 1D launch config
- ✅ rounds up grid size for non-divisible total
- ✅ creates 2D launch config
- ✅ computes total blocks
- ✅ computes threads per block
- ✅ validates valid config
- ✅ rejects zero block size
- ✅ adds shared memory to config
### PTX Builder - Constants

- ✅ loads integer constant
- ✅ loads unsigned integer constant

