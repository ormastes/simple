//! Compute instruction lowering
//!
//! GPU compute instructions (GpuGlobalId, GpuBarrier, GpuAtomic, etc.) are lowered
//! directly in `spirv_instructions.rs` as part of the main instruction lowering pipeline.
//!
//! This separation was originally planned but the unified approach in spirv_instructions.rs
//! proved more maintainable. GPU-specific lowering methods include:
//! - lower_gpu_global_id()
//! - lower_gpu_local_id()
//! - lower_gpu_group_id()
//! - lower_gpu_barrier()
//! - lower_gpu_atomic()
//!
//! See `spirv_instructions.rs` for implementation details.
