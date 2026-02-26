//! MIR instruction definitions.
//!
//! This module defines all MIR instructions, patterns, and related types.
//!
//! # Module Organization
//!
//! The MIR instruction system is split across multiple files for maintainability:
//!
//! - `inst_types.rs` - Supporting types (ParallelBackend, ContractKind, GpuMemoryScope, etc.)
//! - `inst_enum.rs` - MirInst enum definition (80+ instruction variants)
//! - `inst_effects.rs` - HasEffects trait implementation for effect tracking
//! - `inst_helpers.rs` - Helper methods (dest(), uses(), is_async(), is_nogc())
//!
//! # Basic Types
//!
//! - `BlockId` - Basic block identifier
//! - `VReg` - Virtual register for SSA values
//! - `MirInst` - The main instruction enum
//!
//! # Instruction Categories
//!
//! ## Core (6 instructions)
//! - ConstInt, ConstFloat, ConstBool - Load constants
//! - Copy - Copy register value
//! - BinOp, UnaryOp - Arithmetic/logic operations
//!
//! ## Memory (6 instructions)
//! - Load, Store - Memory access
//! - LocalAddr, GetElementPtr - Address calculation
//! - GcAlloc - Explicit GC allocation
//! - Wait - Blocking operation marker
//!
//! ## Pointers (3 instructions)
//! - PointerNew - Allocate pointer wrapper
//! - PointerRef - Create borrow reference
//! - PointerDeref - Dereference pointer
//!
//! ## Collections (7 instructions)
//! - ArrayLit, TupleLit, VecLit - Create collections
//! - DictLit - Create dictionary
//! - IndexGet, IndexSet - Collection indexing
//! - SliceOp - Create slice
//! - Spread - Unpack collection
//!
//! ## SIMD (30+ instructions)
//! - VecSum, VecProduct, VecMin, VecMax - Reductions
//! - VecExtract, VecWith - Lane operations
//! - VecLoad, VecStore, VecGather, VecScatter - Memory operations
//! - VecFma, VecSqrt, VecRecip - Math operations
//! - VecBlend, VecSelect, VecShuffle - Permutations
//!
//! ## Strings (3 instructions)
//! - ConstString, ConstSymbol - String constants
//! - FStringFormat - String interpolation
//!
//! ## Closures (2 instructions)
//! - ClosureCreate - Create closure with captures
//! - IndirectCall - Call through closure/function pointer
//!
//! ## Objects (6 instructions)
//! - StructInit - Initialize struct/class
//! - FieldGet, FieldSet - Field access
//! - MethodCallStatic, MethodCallVirtual - Method dispatch
//! - BuiltinMethod - Built-in method calls
//!
//! ## Patterns (6 instructions)
//! - PatternTest, PatternBind - Pattern matching
//! - EnumDiscriminant, EnumPayload - Enum operations
//! - EnumUnit, EnumWith - Enum construction
//!
//! ## Unions (3 instructions)
//! - UnionDiscriminant, UnionPayload - Union inspection
//! - UnionWrap - Union construction
//!
//! ## Async (5 instructions)
//! - FutureCreate, Await - Async/await
//! - ActorSpawn, ActorSend, ActorRecv - Actor model
//!
//! ## Generators (3 instructions)
//! - GeneratorCreate, Yield, GeneratorNext - Generator support
//!
//! ## Errors (5 instructions)
//! - TryUnwrap - Error handling
//! - OptionSome, OptionNone - Option construction
//! - ResultOk, ResultErr - Result construction
//!
//! ## Contracts (2 instructions)
//! - ContractCheck - Runtime contract verification
//! - ContractOldCapture - Capture values for postconditions
//!
//! ## Coverage (3 instructions)
//! - DecisionProbe - Decision coverage tracking
//! - ConditionProbe - Condition coverage tracking
//! - PathProbe - Path coverage tracking
//!
//! ## Unit Types (3 instructions)
//! - UnitBoundCheck - Runtime bounds checking
//! - UnitWiden, UnitNarrow - Type conversions
//! - UnitSaturate - Saturation arithmetic
//!
//! ## GPU (11 instructions)
//! - GpuGlobalId, GpuLocalId, GpuGroupId - Work item IDs
//! - GpuGlobalSize, GpuLocalSize, GpuNumGroups - Work group info
//! - GpuBarrier, GpuMemFence - Synchronization
//! - GpuAtomic, GpuAtomicCmpXchg - Atomic operations
//! - GpuSharedAlloc - Shared memory allocation
//! - NeighborLoad - SIMD neighbor access
//!
//! ## Parallel Iterators (4 instructions)
//! - ParMap - Parallel map operation
//! - ParReduce - Parallel reduction
//! - ParFilter - Parallel filter
//! - ParForEach - Parallel for-each
//!
//! ## Fallback (2 instructions)
//! - InterpCall, InterpEval - Interpreter fallback (temporary)

use crate::hir::{BinOp, NeighborDirection, PointerKind, TypeId, UnaryOp};

use super::effects::{CallTarget, Effect, HasEffects};

/// Basic block identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

/// Virtual register
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

// Include all submodules (using include! for simplicity)
// This keeps the modular file structure while satisfying Rust's module system
include!("inst_types.rs");
include!("inst_enum.rs");
include!("inst_effects.rs");
include!("inst_helpers.rs");
