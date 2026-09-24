#[cfg(feature = "vulkan")]
struct AsyncSession {
    device: Arc<super::vulkan_graphics_runtime_core::VulkanDevice>,
    device_identity: u64,
    capacity: usize,
    accepting: bool,
    slots: Vec<AsyncSlot>,
    next_sequence: i64,
    published_sequence: i64,
    retired_sequences: HashSet<i64>,
    bounded_waits: i64,
    backpressure_events: i64,
    max_in_flight: i64,
    wait_timeout_ns: u64,
    telemetry: AsyncTelemetry,
    snapshot_token: i64,
    snapshot: [i64; TELEMETRY_WORDS],
}

#[cfg(feature = "vulkan")]
impl AsyncSession {
    fn new(device: Arc<super::vulkan_graphics_runtime_core::VulkanDevice>, capacity: usize) -> Self {
        let device_identity = Arc::as_ptr(&device) as usize as u64;
        Self {
            device,
            device_identity,
            capacity,
            accepting: true,
            slots: (0..capacity).map(|_| AsyncSlot::new()).collect(),
            next_sequence: 1,
            published_sequence: 0,
            retired_sequences: HashSet::with_capacity(capacity),
            bounded_waits: 0,
            backpressure_events: 0,
            max_in_flight: 0,
            wait_timeout_ns: 1_000_000,
            telemetry: AsyncTelemetry::default(),
            snapshot_token: 0,
            snapshot: [0; TELEMETRY_WORDS],
        }
    }

    fn in_flight(&self) -> i64 {
        self.slots.iter().filter(|slot| slot.state != SlotState::Free).count() as i64
    }

    fn free_slot(&self) -> Option<usize> {
        admission_index(&self.slots, self.next_sequence, self.published_sequence)
    }

    fn oldest_submitted(&self) -> Option<usize> {
        self.slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.state == SlotState::Submitted)
            .min_by_key(|(_, slot)| slot.sequence)
            .map(|(index, _)| index)
    }

    fn publish(&mut self, sequence: i64) {
        publish_contiguous(&mut self.published_sequence, &mut self.retired_sequences, sequence);
    }
}

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    static ref ASYNC_SESSIONS: Mutex<HashMap<i64, AsyncSession>> = Mutex::new(HashMap::new());
    /// Serializes operations which move ownership between a session slot and
    /// `STATE`. Polling and counter queries deliberately do not take this gate,
    /// so they remain available while acquire performs its one bounded wait.
    static ref ASYNC_OPERATION_GATE: Mutex<()> = Mutex::new(());
}

#[cfg(feature = "vulkan")]
fn discard_recording_command(device: &Arc<super::vulkan_graphics_runtime_core::VulkanDevice>, command: i64) {
    if command <= 0 {
        return;
    }
    let removed = STATE.lock().compute_commands.remove(&command).is_some();
    if removed {
        device.free_compute_command(vk::CommandBuffer::from_raw(command as u64));
    }
}

#[cfg(feature = "vulkan")]
fn reset_recording_slot(session: i64, token: i64) {
    let mut sessions = ASYNC_SESSIONS.lock();
    let Some(owner) = sessions.get_mut(&session) else {
        return;
    };
    let Some(slot) = owner
        .slots
        .iter_mut()
        .find(|slot| slot.token == token && matches!(slot.state, SlotState::Recording | SlotState::Submitting))
    else {
        return;
    };
    owner.telemetry.released_bytes = owner.telemetry.released_bytes.saturating_add(slot.retained_bytes);
    if !slot.reset_for_reuse() {
        owner.accepting = false;
    }
}

#[cfg(feature = "vulkan")]
fn take_submission(handle: i64) -> Option<QuarantinedComputeSubmission> {
    let mut state = STATE.lock();
    let index = state
        .quarantined_compute
        .iter()
        .position(|submission| submission.wait_handle == handle)?;
    Some(state.quarantined_compute.swap_remove(index))
}

#[cfg(feature = "vulkan")]
fn put_submission(submission: QuarantinedComputeSubmission) {
    STATE.lock().quarantined_compute.push(submission);
}

/// Poll a pending fence without waiting.  This only holds STATE while making
/// the non-blocking Vulkan status query, never across a host wait.
#[cfg(feature = "vulkan")]
fn poll_fence(handle: i64) -> i64 {
    let state = STATE.lock();
    let Some(fence) = state.fence_by_handle(handle) else {
        return ASYNC_INVALID;
    };
    match fence.is_signaled() {
        Ok(true) => ASYNC_RETIRED,
        Ok(false) => ASYNC_PENDING,
        Err(_) => ASYNC_UNKNOWN,
    }
}

/// Prove completion and release one exact quarantined submission.  The fence
/// query is non-blocking; command and owner release occurs only after proof.
#[cfg(feature = "vulkan")]
fn retire_fence(handle: i64) -> i64 {
    let Some(submission) = take_submission(handle) else {
        return ASYNC_INVALID;
    };
    match submission.fence.is_signaled() {
        Ok(true) => {
            let device = submission.device;
            device.free_compute_command(submission.command_buffer);
            let mut state = STATE.lock();
            state.async_compute_session_fences.remove(&handle);
            // Session tokens are consumed on retirement; no unbounded legacy
            // handle tombstone is needed for this private fence.
            drop(submission.owners);
            drop(submission.fence);
            ASYNC_RETIRED
        }
        Ok(false) => {
            put_submission(submission);
            ASYNC_PENDING
        }
        Err(_) => {
            put_submission(submission);
            ASYNC_UNKNOWN
        }
    }
}

/// Pin the fence without removing its registry entry. Other threads can still
/// resolve/poll this exact generation during the bounded wait.
#[cfg(feature = "vulkan")]
fn observe_fence_bounded(handle: i64, timeout_ns: u64) -> i64 {
    let fence = {
        let state = STATE.lock();
        state
            .quarantined_compute
            .iter()
            .find(|s| s.wait_handle == handle)
            .map(|s| s.fence.clone())
    };
    let Some(fence) = fence else {
        return ASYNC_INVALID;
    };
    match fence.wait(timeout_ns) {
        Ok(()) => ASYNC_RETIRED,
        Err(_) => match fence.is_signaled() {
            Ok(true) => ASYNC_RETIRED,
            Ok(false) => ASYNC_PENDING,
            Err(_) => ASYNC_UNKNOWN,
        },
    }
}

#[cfg(feature = "vulkan")]
fn begin_session_command(session_device: &Arc<super::vulkan_graphics_runtime_core::VulkanDevice>) -> i64 {
    let mut state = STATE.lock();
    if !state.quarantined_compute.is_empty()
        && state
            .quarantined_compute
            .iter()
            .any(|entry| Arc::as_ptr(&entry.device) == Arc::as_ptr(session_device) && entry.wait_handle == 0)
    {
        state.set_error("async_session_acquire: completion is unknown".to_string());
        return 0;
    }
    let Ok(device) = state.require_device() else {
        return 0;
    };
    if !Arc::ptr_eq(&device, session_device) {
        state.set_error("async_session_acquire: device generation changed".to_string());
        return 0;
    }
    match device.begin_compute_command() {
        Ok(command_buffer) => {
            let command = command_buffer.as_raw() as i64;
            if command <= 0 || state.compute_commands.contains_key(&command) {
                // No public identity may be zero, negative, or collide. A
                // driver collision preserves the existing command owner rather
                // than freeing a handle that still identifies that command.
                if command <= 0 {
                    device.free_compute_command(command_buffer);
                }
                state.set_error("async_session_acquire: invalid or colliding command identity".to_string());
                return 0;
            }
            state.compute_commands.insert(command, ComputeCommandOwners::default());
            command
        }
        Err(error) => {
            state.set_error(format!("async_session_acquire: {error}"));
            0
        }
    }
}
