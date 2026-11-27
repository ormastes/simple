//! Bounded asynchronous compute submission ring for the interpreter's Vulkan
//! bridge (`VK_STATE` in `gpu.rs`).
//!
//! The compiled runtime owns the same ring in
//! `runtime/src/vulkan_graphics_runtime_async*.rs`, over its ash `STATE`. The
//! interpreter runs compute on the dlopen bridge instead, so a ring living only
//! in the runtime crate could never see the bridge's device, pipelines or
//! command handles. This module is the bridge-side owner. It shares the slot
//! state machine, admission window and receipt publication with the runtime
//! through `simple_runtime::vulkan_async_protocol`, and answers the same status
//! values for the same calls.
//!
//! Ownership: a submitted command buffer and its `VkFence` live in the ring's
//! own table until `retire` (or `recover`) has proof of completion. They are
//! never placed in `quarantined_commands` or `live_fences`, so the device-idle
//! reap and the caller-fence API cannot free them underneath the ring. The
//! pipeline, descriptor sets and buffers a submission recorded stay refused for
//! destruction or rebinding until that submission is released.
//!
//! Everything runs under the single `VK_STATE` mutex. The one bounded wait in
//! `acquire` (ring full, at most the session's `timeout_ns`, <= 1 s) is taken
//! with that mutex held; the interpreter drives the bridge from one thread.
//!
//! Not served here: `snapshot`, `snapshot_word` and `abandon_device` have no
//! bridge handler and fall through to the runtime crate, which does not know a
//! bridge session and answers "unavailable" (-1).

use super::vulkan_dlopen::*;
use super::{arg_i64, CompileError, Value};
use simple_runtime::vulkan_async_protocol::{
    admission_index, publish_contiguous, AsyncSlot, SlotState, ASYNC_CLOSED, ASYNC_INVALID, ASYNC_PENDING,
    ASYNC_RETIRED, ASYNC_UNKNOWN, ASYNC_WOULD_BLOCK,
};
use std::collections::HashSet;
use std::ptr;
use std::sync::atomic::{AtomicI64, Ordering};

const VK_NOT_READY: VkResult = 1;
const VK_TIMEOUT: VkResult = 2;
const VK_ERROR_OUT_OF_HOST_MEMORY: VkResult = -1;
const VK_ERROR_OUT_OF_DEVICE_MEMORY: VkResult = -2;

/// Session, token and caller-visible fence identities. Monotonic and never
/// reused: a raw `VkFence` value may be recycled by the driver after destroy,
/// which would let a stale caller handle alias a newer submission.
static NEXT_RING_HANDLE: AtomicI64 = AtomicI64::new(1);

fn alloc_ring_handle() -> i64 {
    let handle = NEXT_RING_HANDLE.fetch_add(1, Ordering::Relaxed);
    if handle <= 0 {
        NEXT_RING_HANDLE.store(i64::MAX, Ordering::Relaxed);
        return 0;
    }
    handle
}

/// Device objects owned by one accepted submission, plus the bridge handles of
/// every resource its command buffer may still read.
struct RingSubmission {
    fence: u64,
    cmd: VkCommandBuffer,
    pipeline: i64,
    descriptor_sets: Vec<i64>,
    buffers: Vec<i64>,
}

pub struct AsyncRing {
    handle: i64,
    accepting: bool,
    slots: Vec<AsyncSlot>,
    /// Parallel to `slots`. `Some` exactly while the slot is Submitted,
    /// Completed or Unknown.
    owned: Vec<Option<RingSubmission>>,
    next_sequence: i64,
    published_sequence: i64,
    retired_sequences: HashSet<i64>,
    wait_timeout_ns: u64,
    fences_created: i64,
    fences_destroyed: i64,
    commands_begun: i64,
    commands_freed: i64,
}

impl AsyncRing {
    fn new(handle: i64, capacity: usize, wait_timeout_ns: u64) -> Self {
        Self {
            handle,
            accepting: true,
            slots: (0..capacity).map(|_| AsyncSlot::new()).collect(),
            owned: (0..capacity).map(|_| None).collect(),
            next_sequence: 1,
            published_sequence: 0,
            retired_sequences: HashSet::with_capacity(capacity),
            wait_timeout_ns,
            fences_created: 0,
            fences_destroyed: 0,
            commands_begun: 0,
            commands_freed: 0,
        }
    }

    fn in_flight(&self) -> i64 {
        self.slots.iter().filter(|slot| slot.state != SlotState::Free).count() as i64
    }

    fn slot_of(&self, token: i64) -> Option<usize> {
        if token <= 0 {
            return None;
        }
        self.slots.iter().position(|slot| slot.token == token)
    }

    fn reset_slot(&mut self, index: usize) {
        if !self.slots[index].reset_for_reuse() {
            self.accepting = false;
        }
    }
}

/// True while a ring session owns direct compute admission on this device.
pub(super) fn ring_active(s: &VulkanState) -> bool {
    s.async_ring.is_some()
}

/// Refuse a direct compute call while a ring session is open, mirroring the
/// runtime's `async_compute_session_active` gates.
pub(super) fn ring_refuses(s: &mut VulkanState, what: &str) -> bool {
    if !ring_active(s) {
        return false;
    }
    s.last_error = format!("{what}: async compute session owns this device");
    true
}

/// Which resource kind a destroy/rebind call is about to touch.
#[derive(Clone, Copy)]
pub(super) enum RingResource {
    Pipeline,
    DescriptorSet,
    Buffer,
}

/// True (with `last_error` set) when an unreleased ring submission may still
/// read the resource, so the caller must not destroy or rewrite it yet.
pub(super) fn ring_retains(s: &mut VulkanState, kind: RingResource, handle: i64, what: &str) -> bool {
    let retained = s.async_ring.as_ref().is_some_and(|ring| {
        ring.owned.iter().flatten().any(|sub| match kind {
            RingResource::Pipeline => sub.pipeline == handle,
            RingResource::DescriptorSet => sub.descriptor_sets.contains(&handle),
            RingResource::Buffer => sub.buffers.contains(&handle),
        })
    });
    if retained {
        s.last_error = format!("{what}: resource is retained by an in-flight async submission");
    }
    retained
}

fn ring_mut(s: &mut VulkanState, session: i64) -> Option<&mut AsyncRing> {
    s.async_ring
        .as_mut()
        .filter(|ring| session > 0 && ring.handle == session)
}

fn ring_ref(s: &VulkanState, session: i64) -> Option<&AsyncRing> {
    s.async_ring
        .as_ref()
        .filter(|ring| session > 0 && ring.handle == session)
}

/// Free a recording (never submitted) command of the ring.
fn free_recording_command(s: &mut VulkanState, command: i64) {
    let index = command as usize;
    if command <= 0 || index > s.command_buffers.len() {
        return;
    }
    if let Some(entry) = s.command_buffers[index - 1].take() {
        unsafe { (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &entry.cmd) };
        if let Some(ring) = s.async_ring.as_mut() {
            ring.commands_freed += 1;
        }
    }
}

/// Release the device objects of one submission. Only called with completion
/// proof for its fence, or after a successful device-idle wait.
fn release_submission(s: &mut VulkanState, index: usize) {
    let Some(sub) = s.async_ring.as_mut().and_then(|ring| ring.owned[index].take()) else {
        return;
    };
    unsafe {
        (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &sub.cmd);
        (s.fns.destroy_fence)(s.device, sub.fence, ptr::null());
    }
    if let Some(ring) = s.async_ring.as_mut() {
        ring.commands_freed += 1;
        ring.fences_destroyed += 1;
    }
}

/// Non-blocking status of the fence owned by slot `index`.
fn fence_status(s: &VulkanState, index: usize) -> i64 {
    let Some(fence) = s
        .async_ring
        .as_ref()
        .and_then(|ring| ring.owned[index].as_ref())
        .map(|sub| sub.fence)
    else {
        return ASYNC_INVALID;
    };
    match unsafe { (s.fns.get_fence_status)(s.device, fence) } {
        VK_SUCCESS => ASYNC_RETIRED,
        VK_NOT_READY => ASYNC_PENDING,
        _ => ASYNC_UNKNOWN,
    }
}

fn mark_unknown(ring: &mut AsyncRing, index: usize) {
    ring.accepting = false;
    ring.slots[index].state = SlotState::Unknown;
}

fn int(value: i64) -> Result<Value, CompileError> {
    Ok(Value::Int(value))
}

/// `rt_vulkan_async_session_supported() -> i64`
pub fn rt_vulkan_async_session_supported_fn(_args: &[Value]) -> Result<Value, CompileError> {
    int(i64::from(super::check_vulkan_available()))
}

/// `rt_vulkan_async_session_create(capacity) -> session`
pub fn rt_vulkan_async_session_create_fn(args: &[Value]) -> Result<Value, CompileError> {
    let capacity = arg_i64(args, 0, "rt_vulkan_async_session_create", 1)?;
    int(create_session(capacity, 1_000_000))
}

/// `rt_vulkan_async_session_create_with_wait(capacity, timeout_ns) -> session`
pub fn rt_vulkan_async_session_create_with_wait_fn(args: &[Value]) -> Result<Value, CompileError> {
    let capacity = arg_i64(args, 0, "rt_vulkan_async_session_create_with_wait", 2)?;
    let timeout_ns = arg_i64(args, 1, "rt_vulkan_async_session_create_with_wait", 2)?;
    int(create_session(capacity, timeout_ns))
}

fn create_session(capacity: i64, timeout_ns: i64) -> i64 {
    if !(3..=16).contains(&capacity) || !(0..=1_000_000_000).contains(&timeout_ns) {
        return 0;
    }
    let mut guard = VK_STATE.lock().unwrap();
    let Some(s) = guard.as_mut() else {
        return 0;
    };
    if ring_active(s) || s.command_buffers.iter().any(Option::is_some) || !s.quarantined_commands.is_empty() {
        s.last_error = "async_session_create: direct compute owner is already live".to_string();
        return 0;
    }
    let handle = alloc_ring_handle();
    if handle <= 0 {
        s.last_error = "async_session_create: handle allocation exhausted".to_string();
        return 0;
    }
    s.async_ring = Some(AsyncRing::new(handle, capacity as usize, timeout_ns as u64));
    handle
}

/// `rt_vulkan_async_session_acquire(session) -> token`
pub fn rt_vulkan_async_session_acquire_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_acquire", 1)?;
    let mut guard = VK_STATE.lock().unwrap();
    let Some(s) = guard.as_mut() else {
        return int(ASYNC_INVALID);
    };
    let (free, oldest, timeout_ns) = {
        let Some(ring) = ring_mut(s, session) else {
            return int(ASYNC_INVALID);
        };
        if !ring.accepting {
            return int(ASYNC_CLOSED);
        }
        let oldest = ring
            .slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.state == SlotState::Submitted)
            .min_by_key(|(_, slot)| slot.sequence)
            .map(|(index, _)| index);
        (
            admission_index(&ring.slots, ring.next_sequence, ring.published_sequence),
            oldest,
            ring.wait_timeout_ns,
        )
    };
    let Some(index) = free else {
        // Ring full: observe the oldest submission once, with one bounded
        // wait, and report backpressure. The slot is released only by an
        // explicit `retire`.
        let Some(oldest) = oldest else {
            return int(ASYNC_WOULD_BLOCK);
        };
        let mut result = fence_status(s, oldest);
        if result == ASYNC_PENDING && timeout_ns > 0 {
            let fence = s
                .async_ring
                .as_ref()
                .and_then(|ring| ring.owned[oldest].as_ref())
                .map(|sub| sub.fence);
            if let Some(fence) = fence {
                result = match unsafe { (s.fns.wait_for_fences)(s.device, 1, &fence, 1, timeout_ns) } {
                    VK_SUCCESS => ASYNC_RETIRED,
                    VK_TIMEOUT => ASYNC_PENDING,
                    _ => ASYNC_UNKNOWN,
                };
            }
        }
        let Some(ring) = ring_mut(s, session) else {
            return int(ASYNC_UNKNOWN);
        };
        if result == ASYNC_UNKNOWN || result == ASYNC_INVALID {
            mark_unknown(ring, oldest);
            return int(ASYNC_UNKNOWN);
        }
        if result == ASYNC_RETIRED {
            ring.slots[oldest].state = SlotState::Completed;
        }
        return int(ASYNC_WOULD_BLOCK);
    };
    let token = alloc_ring_handle();
    if token <= 0 {
        if let Some(ring) = ring_mut(s, session) {
            ring.accepting = false;
        }
        return int(ASYNC_UNKNOWN);
    }
    let command = super::begin_compute_command(s);
    if command <= 0 {
        return int(ASYNC_INVALID);
    }
    let Some(ring) = ring_mut(s, session) else {
        return int(ASYNC_UNKNOWN);
    };
    ring.commands_begun += 1;
    let slot = &mut ring.slots[index];
    slot.token = token;
    slot.command = command;
    slot.state = SlotState::Recording;
    int(token)
}

/// `rt_vulkan_async_session_command(session, token) -> command`
pub fn rt_vulkan_async_session_command_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_command", 2)?;
    let token = arg_i64(args, 1, "rt_vulkan_async_session_command", 2)?;
    let guard = VK_STATE.lock().unwrap();
    let command = guard
        .as_ref()
        .and_then(|s| ring_ref(s, session))
        .and_then(|ring| ring.slot_of(token).map(|index| &ring.slots[index]))
        .filter(|slot| slot.state == SlotState::Recording)
        .map(|slot| slot.command);
    int(command.unwrap_or(ASYNC_INVALID))
}

/// `rt_vulkan_async_session_submit(session, token) -> fence`
pub fn rt_vulkan_async_session_submit_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_submit", 2)?;
    let token = arg_i64(args, 1, "rt_vulkan_async_session_submit", 2)?;
    let mut guard = VK_STATE.lock().unwrap();
    let Some(s) = guard.as_mut() else {
        return int(ASYNC_INVALID);
    };
    let (index, command, sequence) = {
        let Some(ring) = ring_mut(s, session) else {
            return int(ASYNC_INVALID);
        };
        if !ring.accepting || ring.next_sequence <= 0 || ring.next_sequence == i64::MAX {
            ring.accepting = false;
            return int(ASYNC_CLOSED);
        }
        let Some(index) = ring
            .slot_of(token)
            .filter(|&index| ring.slots[index].state == SlotState::Recording && ring.slots[index].command > 0)
        else {
            return int(ASYNC_INVALID);
        };
        (index, ring.slots[index].command, ring.next_sequence)
    };
    // The recording command leaves the direct-command table here: from now on
    // it is either submitted and ring-owned, or freed.
    let entry = match s.command_buffers.get_mut(command as usize - 1).and_then(Option::take) {
        Some(entry) => entry,
        None => {
            if let Some(ring) = ring_mut(s, session) {
                ring.reset_slot(index);
            }
            return int(ASYNC_INVALID);
        }
    };
    let cmd = entry.cmd;
    let fail_unsubmitted = |s: &mut VulkanState, error: String, result: i64| {
        unsafe { (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &cmd) };
        s.last_error = error;
        if let Some(ring) = ring_mut(s, session) {
            ring.commands_freed += 1;
            ring.reset_slot(index);
        }
        int(result)
    };
    // Reserve the caller-visible name before queue acceptance: exhaustion must
    // not create accepted work without a resolvable fence identity.
    let handle = alloc_ring_handle();
    if handle <= 0 {
        return fail_unsubmitted(
            s,
            "async_session_submit: fence handle allocation exhausted".to_string(),
            ASYNC_INVALID,
        );
    }
    let info = VkFenceCreateInfo {
        s_type: 8,
        p_next: ptr::null(),
        flags: 0,
    };
    let mut fence = 0;
    let created = unsafe { (s.fns.create_fence)(s.device, &info, ptr::null(), &mut fence) };
    if created != VK_SUCCESS {
        return fail_unsubmitted(s, format!("async_session_submit fence: VkResult {created}"), 0);
    }
    let buffers = entry
        .descriptor_sets
        .iter()
        .filter_map(|&set| s.descriptor_sets.get(set as usize - 1).and_then(Option::as_ref))
        .flat_map(|set| set.buffers.iter().map(|&(_, buffer)| buffer))
        .collect();
    let submission = RingSubmission {
        fence,
        cmd,
        pipeline: entry.pipeline_handle,
        descriptor_sets: entry.descriptor_sets,
        buffers,
    };
    let submit = VkSubmitInfo {
        s_type: 4,
        p_next: ptr::null(),
        wait_semaphore_count: 0,
        p_wait_semaphores: ptr::null(),
        p_wait_dst_stage_mask: ptr::null(),
        command_buffer_count: 1,
        p_command_buffers: &cmd,
        signal_semaphore_count: 0,
        p_signal_semaphores: ptr::null(),
    };
    let submitted = unsafe { (s.fns.queue_submit)(s.queue, 1, &submit, fence) };
    if submitted == VK_ERROR_OUT_OF_HOST_MEMORY || submitted == VK_ERROR_OUT_OF_DEVICE_MEMORY {
        // Definitely not accepted by the queue: nothing can still read it.
        unsafe { (s.fns.destroy_fence)(s.device, fence, ptr::null()) };
        return fail_unsubmitted(s, format!("async_session_submit: VkResult {submitted}"), 0);
    }
    if submitted == VK_SUCCESS {
        s.accepted_compute_submit_count += 1;
    } else {
        s.last_error = format!("async_session_submit completion unknown: VkResult {submitted}");
    }
    let Some(ring) = ring_mut(s, session) else {
        return int(ASYNC_UNKNOWN);
    };
    ring.fences_created += 1;
    ring.owned[index] = Some(submission);
    ring.slots[index].sequence = sequence;
    ring.next_sequence = sequence + 1;
    if submitted != VK_SUCCESS {
        // Acceptance is ambiguous: keep the command and fence owned and close
        // admission until explicit recovery.
        mark_unknown(ring, index);
        return int(ASYNC_UNKNOWN);
    }
    ring.slots[index].fence = handle;
    ring.slots[index].state = SlotState::Submitted;
    int(handle)
}

/// `rt_vulkan_async_session_poll(session, token) -> status`
pub fn rt_vulkan_async_session_poll_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_poll", 2)?;
    let token = arg_i64(args, 1, "rt_vulkan_async_session_poll", 2)?;
    let mut guard = VK_STATE.lock().unwrap();
    let Some(s) = guard.as_mut() else {
        return int(ASYNC_INVALID);
    };
    let index = {
        let Some(ring) = ring_ref(s, session) else {
            return int(ASYNC_INVALID);
        };
        let Some(index) = ring.slot_of(token) else {
            return int(ASYNC_INVALID);
        };
        match ring.slots[index].state {
            SlotState::Unknown => return int(ASYNC_UNKNOWN),
            SlotState::Completed => return int(ASYNC_RETIRED),
            SlotState::Submitted => index,
            _ => return int(ASYNC_INVALID),
        }
    };
    let result = fence_status(s, index);
    let Some(ring) = ring_mut(s, session) else {
        return int(ASYNC_INVALID);
    };
    match result {
        ASYNC_RETIRED => ring.slots[index].state = SlotState::Completed,
        ASYNC_PENDING => {}
        _ => {
            mark_unknown(ring, index);
            return int(ASYNC_UNKNOWN);
        }
    }
    int(result)
}

/// `rt_vulkan_async_session_retire(session, token) -> status`
pub fn rt_vulkan_async_session_retire_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_retire", 2)?;
    let token = arg_i64(args, 1, "rt_vulkan_async_session_retire", 2)?;
    let mut guard = VK_STATE.lock().unwrap();
    let Some(s) = guard.as_mut() else {
        return int(ASYNC_INVALID);
    };
    let (index, sequence) = {
        let Some(ring) = ring_ref(s, session) else {
            return int(ASYNC_INVALID);
        };
        let Some(index) = ring.slot_of(token) else {
            return int(ASYNC_INVALID);
        };
        match ring.slots[index].state {
            SlotState::Submitted => return int(ASYNC_PENDING),
            SlotState::Unknown => return int(ASYNC_UNKNOWN),
            SlotState::Completed => {}
            SlotState::Free | SlotState::Recording | SlotState::Submitting | SlotState::Retiring => {
                return int(ASYNC_INVALID)
            }
        }
        (index, ring.slots[index].sequence)
    };
    // Prove completion again on the exact fence before releasing anything.
    let result = fence_status(s, index);
    if result == ASYNC_RETIRED {
        release_submission(s, index);
    }
    let Some(ring) = ring_mut(s, session) else {
        return int(ASYNC_UNKNOWN);
    };
    match result {
        ASYNC_RETIRED => {
            publish_contiguous(&mut ring.published_sequence, &mut ring.retired_sequences, sequence);
            ring.reset_slot(index);
        }
        ASYNC_PENDING => {}
        _ => {
            mark_unknown(ring, index);
            return int(ASYNC_UNKNOWN);
        }
    }
    int(result)
}

/// `rt_vulkan_async_session_receipt(session, sequence) -> 0|1`
pub fn rt_vulkan_async_session_receipt_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_receipt", 2)?;
    let sequence = arg_i64(args, 1, "rt_vulkan_async_session_receipt", 2)?;
    let guard = VK_STATE.lock().unwrap();
    let published = guard
        .as_ref()
        .and_then(|s| ring_ref(s, session))
        .map(|ring| i64::from(sequence > 0 && sequence <= ring.published_sequence));
    int(published.unwrap_or(0))
}

/// `rt_vulkan_async_session_cancel(session) -> 1|-1`
pub fn rt_vulkan_async_session_cancel_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_cancel", 1)?;
    let mut guard = VK_STATE.lock().unwrap();
    let Some(ring) = guard.as_mut().and_then(|s| ring_mut(s, session)) else {
        return int(ASYNC_INVALID);
    };
    ring.accepting = false;
    int(1)
}

/// `rt_vulkan_async_session_close(session) -> 1 closed | 0 still in flight | -2 unknown`
pub fn rt_vulkan_async_session_close_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_close", 1)?;
    let mut guard = VK_STATE.lock().unwrap();
    let Some(s) = guard.as_mut() else {
        return int(1);
    };
    let recording: Vec<(usize, i64)> = {
        let Some(ring) = ring_mut(s, session) else {
            return int(1);
        };
        ring.accepting = false;
        ring.slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.state == SlotState::Recording)
            .map(|(index, slot)| (index, slot.command))
            .collect()
    };
    for (index, command) in recording {
        free_recording_command(s, command);
        if let Some(ring) = ring_mut(s, session) {
            ring.reset_slot(index);
        }
    }
    let Some(ring) = ring_mut(s, session) else {
        return int(1);
    };
    if ring.in_flight() != 0 {
        if ring.slots.iter().any(|slot| slot.state == SlotState::Unknown) {
            return int(ASYNC_UNKNOWN);
        }
        return int(0);
    }
    // Fail closed on an accounting mismatch: a session that cannot prove every
    // command buffer and fence it created was released is not reported closed.
    let balanced = ring.owned.iter().all(Option::is_none)
        && ring.fences_created == ring.fences_destroyed
        && ring.commands_begun == ring.commands_freed;
    if !balanced {
        let error = format!(
            "async_session_close: owner accounting mismatch (fences {}/{}, commands {}/{})",
            ring.fences_destroyed, ring.fences_created, ring.commands_freed, ring.commands_begun
        );
        s.last_error = error;
        return int(0);
    }
    s.async_ring = None;
    int(1)
}

/// `rt_vulkan_async_session_capacity(session) -> capacity | 0`
pub fn rt_vulkan_async_session_capacity_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_capacity", 1)?;
    let guard = VK_STATE.lock().unwrap();
    let capacity = guard
        .as_ref()
        .and_then(|s| ring_ref(s, session))
        .map(|ring| ring.slots.len() as i64);
    int(capacity.unwrap_or(0))
}

/// `rt_vulkan_async_session_in_flight(session) -> count | -1`
pub fn rt_vulkan_async_session_in_flight_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_in_flight", 1)?;
    let guard = VK_STATE.lock().unwrap();
    let in_flight = guard
        .as_ref()
        .and_then(|s| ring_ref(s, session))
        .map(AsyncRing::in_flight);
    int(in_flight.unwrap_or(-1))
}

/// `rt_vulkan_async_session_published_sequence(session) -> sequence | -1`
pub fn rt_vulkan_async_session_published_sequence_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_published_sequence", 1)?;
    let guard = VK_STATE.lock().unwrap();
    let published = guard
        .as_ref()
        .and_then(|s| ring_ref(s, session))
        .map(|ring| ring.published_sequence);
    int(published.unwrap_or(-1))
}

/// `rt_vulkan_async_session_recover(session) -> 1 | -2 | -1`
///
/// Explicit recovery: close admission, wait for device idle once, then release
/// every command and fence the session still owns. It never publishes receipts
/// for submissions that were not retired; the caller closes the session after.
pub fn rt_vulkan_async_session_recover_fn(args: &[Value]) -> Result<Value, CompileError> {
    let session = arg_i64(args, 0, "rt_vulkan_async_session_recover", 1)?;
    let mut guard = VK_STATE.lock().unwrap();
    let Some(s) = guard.as_mut() else {
        return int(ASYNC_INVALID);
    };
    let Some(ring) = ring_mut(s, session) else {
        return int(ASYNC_INVALID);
    };
    ring.accepting = false;
    let capacity = ring.slots.len();
    let idle = unsafe { (s.fns.device_wait_idle)(s.device) };
    if idle != VK_SUCCESS {
        s.last_error = format!("async_session_recover: VkResult {idle}");
        return int(ASYNC_UNKNOWN);
    }
    for index in 0..capacity {
        release_submission(s, index);
        let recording = ring_ref(s, session)
            .map(|ring| &ring.slots[index])
            .filter(|slot| slot.state == SlotState::Recording)
            .map(|slot| slot.command);
        if let Some(command) = recording {
            free_recording_command(s, command);
        }
        if let Some(ring) = ring_mut(s, session) {
            // Admission stays closed, so an exhausted generation is harmless.
            let _ = ring.slots[index].reset_for_reuse();
        }
    }
    if let Some(ring) = ring_mut(s, session) {
        ring.retired_sequences.clear();
    }
    int(ASYNC_RETIRED)
}
