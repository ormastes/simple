//! Runtime-owned bounded asynchronous compute submission sessions.
//!
//! A session is the sole admission owner for one Vulkan device generation.
//! Simple receives opaque slot tokens; command buffers, fences, and retained
//! Vulkan owners stay in the runtime until exact fence retirement.  The
//! bounded wait path pins the exact fence lease outside `STATE` before
//! waiting, so the global runtime registry is never held across a host wait.

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{
    alloc_handle, vk, ComputeCommandOwners, Fence, QuarantinedComputeSubmission, STATE,
};
#[cfg(feature = "vulkan")]
use crate::vulkan::device::FencedSubmitError;
#[cfg(feature = "vulkan")]
use ash::vk::Handle;
#[cfg(feature = "vulkan")]
use parking_lot::Mutex;
#[cfg(feature = "vulkan")]
use std::collections::{HashMap, HashSet};
#[cfg(feature = "vulkan")]
use std::sync::Arc;
#[cfg(feature = "vulkan")]
use std::time::Instant;

// Status values and the slot protocol are shared with the interpreter bridge's
// ring owner; see `crate::vulkan_async_protocol`.
pub use crate::vulkan_async_protocol::{
    ASYNC_CLOSED, ASYNC_INVALID, ASYNC_PENDING, ASYNC_QUARANTINED, ASYNC_RETIRED, ASYNC_UNKNOWN, ASYNC_WOULD_BLOCK,
};
#[cfg(feature = "vulkan")]
use crate::vulkan_async_protocol::*;

// Included files share this private owner module and do not expose mutable
// runtime internals to other subsystems.
include!("vulkan_graphics_runtime_async_owner.rs");
include!("vulkan_graphics_runtime_async_offer.rs");
include!("vulkan_graphics_runtime_async_observe.rs");
include!("vulkan_graphics_runtime_async_lifecycle.rs");
include!("vulkan_graphics_runtime_async_telemetry.rs");
include!("vulkan_graphics_runtime_async_recovery.rs");
