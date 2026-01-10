//! GPU Intrinsics
//!
//! This module defines the built-in functions available in GPU kernels.

/// GPU built-in functions for kernel code.
///
/// These represent the intrinsics available inside `#[gpu]` functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuIntrinsic {
    // Work item identification
    /// Get global work item ID (1D).
    GlobalId,
    /// Get global work item ID (per dimension).
    GlobalIdDim,
    /// Get local work item ID within work group (1D).
    LocalId,
    /// Get local work item ID (per dimension).
    LocalIdDim,
    /// Get work group ID (1D).
    GroupId,
    /// Get work group ID (per dimension).
    GroupIdDim,
    /// Get total global size (1D).
    GlobalSize,
    /// Get total global size (per dimension).
    GlobalSizeDim,
    /// Get local work group size (1D).
    LocalSize,
    /// Get local work group size (per dimension).
    LocalSizeDim,
    /// Get number of work groups (1D).
    NumGroups,
    /// Get number of work groups (per dimension).
    NumGroupsDim,

    // Synchronization
    /// Work group barrier (synchronize all threads in work group).
    Barrier,
    /// Memory fence (ensure writes are visible).
    MemFence,
    /// Combined barrier and memory fence.
    BarrierAndFence,

    // Atomic operations
    /// Atomic add.
    AtomicAdd,
    /// Atomic subtract.
    AtomicSub,
    /// Atomic minimum.
    AtomicMin,
    /// Atomic maximum.
    AtomicMax,
    /// Atomic AND.
    AtomicAnd,
    /// Atomic OR.
    AtomicOr,
    /// Atomic XOR.
    AtomicXor,
    /// Atomic exchange.
    AtomicExchange,
    /// Atomic compare-and-exchange.
    AtomicCompareExchange,

    // Math functions
    /// Square root.
    Sqrt,
    /// Reciprocal square root.
    Rsqrt,
    /// Absolute value.
    Abs,
    /// Floor.
    Floor,
    /// Ceiling.
    Ceil,
    /// Round to nearest.
    Round,
    /// Truncate.
    Trunc,
    /// Fused multiply-add.
    Fma,
    /// Minimum.
    Min,
    /// Maximum.
    Max,
    /// Clamp to range.
    Clamp,
    /// Mix/lerp.
    Mix,
    /// Sign.
    Sign,

    // Trigonometric
    /// Sine.
    Sin,
    /// Cosine.
    Cos,
    /// Tangent.
    Tan,
    /// Arc sine.
    Asin,
    /// Arc cosine.
    Acos,
    /// Arc tangent.
    Atan,
    /// Two-argument arc tangent.
    Atan2,

    // Exponential/logarithmic
    /// Exponential (e^x).
    Exp,
    /// Natural logarithm.
    Log,
    /// Base-2 exponential.
    Exp2,
    /// Base-2 logarithm.
    Log2,
    /// Power.
    Pow,
}

impl GpuIntrinsic {
    /// Get the name of this intrinsic as it appears in Simple code.
    pub fn name(&self) -> &'static str {
        match self {
            GpuIntrinsic::GlobalId => "gpu.global_id",
            GpuIntrinsic::GlobalIdDim => "gpu.global_id",
            GpuIntrinsic::LocalId => "gpu.local_id",
            GpuIntrinsic::LocalIdDim => "gpu.local_id",
            GpuIntrinsic::GroupId => "gpu.group_id",
            GpuIntrinsic::GroupIdDim => "gpu.group_id",
            GpuIntrinsic::GlobalSize => "gpu.global_size",
            GpuIntrinsic::GlobalSizeDim => "gpu.global_size",
            GpuIntrinsic::LocalSize => "gpu.local_size",
            GpuIntrinsic::LocalSizeDim => "gpu.local_size",
            GpuIntrinsic::NumGroups => "gpu.num_groups",
            GpuIntrinsic::NumGroupsDim => "gpu.num_groups",

            GpuIntrinsic::Barrier => "gpu.barrier",
            GpuIntrinsic::MemFence => "gpu.mem_fence",
            GpuIntrinsic::BarrierAndFence => "gpu.barrier_and_fence",

            GpuIntrinsic::AtomicAdd => "gpu.atomic_add",
            GpuIntrinsic::AtomicSub => "gpu.atomic_sub",
            GpuIntrinsic::AtomicMin => "gpu.atomic_min",
            GpuIntrinsic::AtomicMax => "gpu.atomic_max",
            GpuIntrinsic::AtomicAnd => "gpu.atomic_and",
            GpuIntrinsic::AtomicOr => "gpu.atomic_or",
            GpuIntrinsic::AtomicXor => "gpu.atomic_xor",
            GpuIntrinsic::AtomicExchange => "gpu.atomic_exchange",
            GpuIntrinsic::AtomicCompareExchange => "gpu.atomic_compare_exchange",

            GpuIntrinsic::Sqrt => "gpu.sqrt",
            GpuIntrinsic::Rsqrt => "gpu.rsqrt",
            GpuIntrinsic::Abs => "gpu.abs",
            GpuIntrinsic::Floor => "gpu.floor",
            GpuIntrinsic::Ceil => "gpu.ceil",
            GpuIntrinsic::Round => "gpu.round",
            GpuIntrinsic::Trunc => "gpu.trunc",
            GpuIntrinsic::Fma => "gpu.fma",
            GpuIntrinsic::Min => "gpu.min",
            GpuIntrinsic::Max => "gpu.max",
            GpuIntrinsic::Clamp => "gpu.clamp",
            GpuIntrinsic::Mix => "gpu.mix",
            GpuIntrinsic::Sign => "gpu.sign",

            GpuIntrinsic::Sin => "gpu.sin",
            GpuIntrinsic::Cos => "gpu.cos",
            GpuIntrinsic::Tan => "gpu.tan",
            GpuIntrinsic::Asin => "gpu.asin",
            GpuIntrinsic::Acos => "gpu.acos",
            GpuIntrinsic::Atan => "gpu.atan",
            GpuIntrinsic::Atan2 => "gpu.atan2",

            GpuIntrinsic::Exp => "gpu.exp",
            GpuIntrinsic::Log => "gpu.log",
            GpuIntrinsic::Exp2 => "gpu.exp2",
            GpuIntrinsic::Log2 => "gpu.log2",
            GpuIntrinsic::Pow => "gpu.pow",
        }
    }

    /// Get the return type for this intrinsic.
    pub fn return_type(&self) -> &'static str {
        match self {
            GpuIntrinsic::GlobalId
            | GpuIntrinsic::GlobalIdDim
            | GpuIntrinsic::LocalId
            | GpuIntrinsic::LocalIdDim
            | GpuIntrinsic::GroupId
            | GpuIntrinsic::GroupIdDim
            | GpuIntrinsic::GlobalSize
            | GpuIntrinsic::GlobalSizeDim
            | GpuIntrinsic::LocalSize
            | GpuIntrinsic::LocalSizeDim
            | GpuIntrinsic::NumGroups
            | GpuIntrinsic::NumGroupsDim => "u32",

            GpuIntrinsic::Barrier | GpuIntrinsic::MemFence | GpuIntrinsic::BarrierAndFence => {
                "unit"
            }

            GpuIntrinsic::AtomicAdd
            | GpuIntrinsic::AtomicSub
            | GpuIntrinsic::AtomicMin
            | GpuIntrinsic::AtomicMax
            | GpuIntrinsic::AtomicAnd
            | GpuIntrinsic::AtomicOr
            | GpuIntrinsic::AtomicXor
            | GpuIntrinsic::AtomicExchange
            | GpuIntrinsic::AtomicCompareExchange => "varies", // Same as operand type

            _ => "varies", // Math functions return same type as input
        }
    }

    /// Check if this intrinsic is a synchronization operation.
    pub fn is_sync(&self) -> bool {
        matches!(
            self,
            GpuIntrinsic::Barrier | GpuIntrinsic::MemFence | GpuIntrinsic::BarrierAndFence
        )
    }

    /// Check if this intrinsic is an atomic operation.
    pub fn is_atomic(&self) -> bool {
        matches!(
            self,
            GpuIntrinsic::AtomicAdd
                | GpuIntrinsic::AtomicSub
                | GpuIntrinsic::AtomicMin
                | GpuIntrinsic::AtomicMax
                | GpuIntrinsic::AtomicAnd
                | GpuIntrinsic::AtomicOr
                | GpuIntrinsic::AtomicXor
                | GpuIntrinsic::AtomicExchange
                | GpuIntrinsic::AtomicCompareExchange
        )
    }
}

/// Represents state for a single GPU work item during software execution.
#[derive(Debug, Clone)]
pub struct WorkItemState {
    /// Global work item ID.
    pub global_id: [u32; 3],
    /// Local work item ID within work group.
    pub local_id: [u32; 3],
    /// Work group ID.
    pub group_id: [u32; 3],
    /// Total global size.
    pub global_size: [u32; 3],
    /// Local work group size.
    pub local_size: [u32; 3],
    /// Number of work groups.
    pub num_groups: [u32; 3],
}

impl WorkItemState {
    /// Create a new work item state.
    pub fn new(
        global_id: [u32; 3],
        local_id: [u32; 3],
        group_id: [u32; 3],
        global_size: [u32; 3],
        local_size: [u32; 3],
    ) -> Self {
        let num_groups = [
            global_size[0].div_ceil(local_size[0]),
            global_size[1].div_ceil(local_size[1]),
            global_size[2].div_ceil(local_size[2]),
        ];

        WorkItemState {
            global_id,
            local_id,
            group_id,
            global_size,
            local_size,
            num_groups,
        }
    }

    /// Create a work item state for 1D execution.
    pub fn new_1d(global_id: u32, global_size: u32, local_size: u32) -> Self {
        let group_id = global_id / local_size;
        let local_id = global_id % local_size;

        Self::new(
            [global_id, 0, 0],
            [local_id, 0, 0],
            [group_id, 0, 0],
            [global_size, 1, 1],
            [local_size, 1, 1],
        )
    }

    /// Get the linear global ID.
    pub fn global_id_linear(&self) -> u32 {
        self.global_id[0]
            + self.global_id[1] * self.global_size[0]
            + self.global_id[2] * self.global_size[0] * self.global_size[1]
    }
}

/// GPU memory fence types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryScope {
    /// Work group scope (shared memory).
    WorkGroup,
    /// Device scope (global memory).
    Device,
    /// All scopes.
    All,
}

/// Atomic memory ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryOrder {
    /// Relaxed ordering.
    Relaxed,
    /// Acquire ordering.
    Acquire,
    /// Release ordering.
    Release,
    /// Acquire-release ordering.
    AcquireRelease,
    /// Sequentially consistent ordering.
    SeqCst,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intrinsic_names() {
        assert_eq!(GpuIntrinsic::GlobalId.name(), "gpu.global_id");
        assert_eq!(GpuIntrinsic::Barrier.name(), "gpu.barrier");
        assert_eq!(GpuIntrinsic::AtomicAdd.name(), "gpu.atomic_add");
    }

    #[test]
    fn test_intrinsic_classification() {
        assert!(GpuIntrinsic::Barrier.is_sync());
        assert!(!GpuIntrinsic::GlobalId.is_sync());

        assert!(GpuIntrinsic::AtomicAdd.is_atomic());
        assert!(!GpuIntrinsic::Sqrt.is_atomic());
    }

    #[test]
    fn test_work_item_state() {
        let state = WorkItemState::new_1d(5, 100, 32);

        assert_eq!(state.global_id[0], 5);
        assert_eq!(state.local_id[0], 5);
        assert_eq!(state.group_id[0], 0);
        assert_eq!(state.global_size[0], 100);
        assert_eq!(state.local_size[0], 32);
    }

    #[test]
    fn test_work_item_linear_id() {
        let state = WorkItemState::new([5, 3, 2], [1, 1, 0], [1, 1, 2], [10, 10, 10], [4, 4, 1]);

        assert_eq!(state.global_id_linear(), 5 + 3 * 10 + 2 * 100);
    }
}
