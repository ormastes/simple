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

/// A completed slot has been proven signaled but remains reserved until the
/// owner explicitly calls retire.  `UNKNOWN` is terminal for admission and
/// keeps the runtime owners quarantined until device recovery/teardown.
pub const ASYNC_RETIRED: i64 = 1;
pub const ASYNC_PENDING: i64 = 0;
pub const ASYNC_INVALID: i64 = -1;
pub const ASYNC_UNKNOWN: i64 = -2;
pub const ASYNC_WOULD_BLOCK: i64 = -3;
pub const ASYNC_CLOSED: i64 = -4;
/// Device generation detached into bounded quarantine; this is NOT completion.
pub const ASYNC_QUARANTINED: i64 = 2;

#[path = "vulkan_async_protocol.rs"]
mod protocol;
#[cfg(feature = "vulkan")]
use protocol::*;

// Included files share this private owner module and do not expose mutable
// runtime internals to other subsystems.
include!("vulkan_graphics_runtime_async_owner.rs");
include!("vulkan_graphics_runtime_async_offer.rs");
include!("vulkan_graphics_runtime_async_observe.rs");
include!("vulkan_graphics_runtime_async_lifecycle.rs");
include!("vulkan_graphics_runtime_async_telemetry.rs");
include!("vulkan_graphics_runtime_async_recovery.rs");
