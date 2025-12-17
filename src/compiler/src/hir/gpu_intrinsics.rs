// GPU and SIMD intrinsic kinds for HIR types module

pub enum GpuIntrinsicKind {
    /// Get global work item ID for a dimension
    GlobalId,
    /// Get local work item ID within work group
    LocalId,
    /// Get work group ID
    GroupId,
    /// Get global work size
    GlobalSize,
    /// Get local work group size
    LocalSize,
    /// Get number of work groups
    NumGroups,
    /// Work group barrier
    Barrier,
    /// Memory fence
    MemFence,
    /// SIMD linear global index: this.index()
    SimdIndex,
    /// SIMD thread index within group: this.thread_index()
    SimdThreadIndex,
    /// SIMD group index: this.group_index()
    SimdGroupIndex,
    /// SIMD vector reduction: sum all lanes
    SimdSum,
    /// SIMD vector reduction: product of all lanes
    SimdProduct,
    /// SIMD vector reduction: minimum of all lanes
    SimdMin,
    /// SIMD vector reduction: maximum of all lanes
    SimdMax,
    /// SIMD vector reduction: all lanes are true (bool vector)
    SimdAll,
    /// SIMD vector reduction: any lane is true (bool vector)
    SimdAny,
    /// SIMD lane extract: v[idx] -> element
    SimdExtract,
    /// SIMD lane insert: v.with(idx, val) -> new vector with lane replaced
    SimdWith,
    /// SIMD element-wise sqrt: v.sqrt()
    SimdSqrt,
    /// SIMD element-wise abs: v.abs()
    SimdAbs,
    /// SIMD element-wise floor: v.floor()
    SimdFloor,
    /// SIMD element-wise ceil: v.ceil()
    SimdCeil,
    /// SIMD element-wise round: v.round()
    SimdRound,
    /// SIMD shuffle: v.shuffle([3, 2, 1, 0]) -> reordered vector
    SimdShuffle,
    /// SIMD blend: a.blend(b, [0, 1, 4, 5]) -> merged vector (0-N from a, N-2N from b)
    SimdBlend,
    /// SIMD masked select: mask.select(a, b) -> select from a where true, b where false
    SimdSelect,
    /// GPU atomic add: gpu.atomic_add(ptr, val) -> old value
    GpuAtomicAdd,
    /// GPU atomic subtract: gpu.atomic_sub(ptr, val) -> old value
    GpuAtomicSub,
    /// GPU atomic min: gpu.atomic_min(ptr, val) -> old value
    GpuAtomicMin,
    /// GPU atomic max: gpu.atomic_max(ptr, val) -> old value
    GpuAtomicMax,
    /// GPU atomic and: gpu.atomic_and(ptr, val) -> old value
    GpuAtomicAnd,
    /// GPU atomic or: gpu.atomic_or(ptr, val) -> old value
    GpuAtomicOr,
    /// GPU atomic xor: gpu.atomic_xor(ptr, val) -> old value
    GpuAtomicXor,
    /// GPU atomic exchange: gpu.atomic_exchange(ptr, val) -> old value
    GpuAtomicExchange,
    /// GPU atomic compare exchange: gpu.atomic_compare_exchange(ptr, expected, desired) -> (old_value, success)
    GpuAtomicCompareExchange,
    /// SIMD load from array: f32x4.load(arr, offset) -> vec
    SimdLoad,
    /// SIMD store to array: v.store(arr, offset)
    SimdStore,
    /// SIMD gather (indexed load): f32x4.gather(arr, indices) -> vec
    SimdGather,
    /// SIMD scatter (indexed store): v.scatter(arr, indices)
    SimdScatter,
    /// SIMD fused multiply-add: v.fma(b, c) -> v * b + c
    SimdFma,
    /// SIMD reciprocal: v.recip() -> 1.0 / v
    SimdRecip,
    /// SIMD neighbor access (left): x.left_neighbor -> element at index-1
    SimdNeighborLeft,
    /// SIMD neighbor access (right): x.right_neighbor -> element at index+1
    SimdNeighborRight,
    /// SIMD masked load: f32x4.load_masked(arr, offset, mask, default) -> vec
    SimdMaskedLoad,
    /// SIMD masked store: v.store_masked(arr, offset, mask)
    SimdMaskedStore,
    /// SIMD element-wise minimum: a.min(b) -> element-wise min of two vectors
    SimdMinVec,
    /// SIMD element-wise maximum: a.max(b) -> element-wise max of two vectors
    SimdMaxVec,
    /// SIMD clamp: v.clamp(lo, hi) -> element-wise clamp to range
    SimdClamp,
}
