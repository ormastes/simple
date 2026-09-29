#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_create(capacity: i64) -> i64 {
    rt_vulkan_async_session_create_with_wait(capacity, 1_000_000)
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_create_with_wait(capacity: i64, timeout_ns: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let _operation = ASYNC_OPERATION_GATE.lock();
        if !(3..=16).contains(&capacity) || !(0..=1_000_000_000).contains(&timeout_ns) {
            return 0;
        }
        if !ASYNC_SESSIONS.lock().is_empty() {
            return 0;
        }
        let (device, handle) = {
            let mut state = STATE.lock();
            if state.async_compute_session_active
                || !state.compute_commands.is_empty()
                || !state.quarantined_compute.is_empty()
            {
                state.set_error("async_session_create: direct compute owner is already live".to_string());
                return 0;
            }
            let Ok(device) = state.require_device() else {
                state.set_error("async_session_create: Vulkan device not initialised".to_string());
                return 0;
            };
            let handle = alloc_handle();
            if handle <= 0 {
                state.set_error("async_session_create: handle allocation exhausted".to_string());
                return 0;
            }
            state.async_compute_session_active = true;
            (device, handle)
        };
        let mut owner = AsyncSession::new(device, capacity as usize);
        owner.wait_timeout_ns = timeout_ns as u64;
        ASYNC_SESSIONS.lock().insert(handle, owner);
        return handle;
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (capacity, timeout_ns);
        0
    }
}

fn session_acquire_impl(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let _operation = ASYNC_OPERATION_GATE.lock();
        let (token, command_owner) = {
            let mut sessions = ASYNC_SESSIONS.lock();
            let Some(owner) = sessions.get_mut(&session) else {
                return ASYNC_INVALID;
            };
            if !owner.accepting {
                return ASYNC_CLOSED;
            }
            let Some(index) = owner.free_slot() else {
                owner.backpressure_events += 1;
                let Some(oldest) = owner.oldest_submitted() else {
                    return ASYNC_WOULD_BLOCK;
                };
                let fence = owner.slots[oldest].fence;
                let timeout_ns = owner.wait_timeout_ns;
                // Poll once before applying the one bounded N2 wait. Both
                // observations happen without the session mutex held.
                drop(sessions);
                let poll_start = Instant::now();
                let polled = poll_fence(fence);
                record_observation(session, Metric::Poll, elapsed_ns(poll_start), polled);
                let wait_start = Instant::now();
                let result = if polled == ASYNC_PENDING && timeout_ns > 0 {
                    observe_fence_bounded(fence, timeout_ns)
                } else {
                    polled
                };
                if polled == ASYNC_PENDING && timeout_ns > 0 {
                    record_observation(session, Metric::Wait, elapsed_ns(wait_start), result);
                }
                let mut sessions = ASYNC_SESSIONS.lock();
                let Some(owner) = sessions.get_mut(&session) else {
                    return ASYNC_UNKNOWN;
                };
                if polled == ASYNC_PENDING && timeout_ns > 0 {
                    owner.bounded_waits += 1;
                }
                let Some(slot_index) = owner.slots.iter().position(|slot| slot.fence == fence) else {
                    // A concurrent explicit retirement made progress while
                    // this caller was observing pressure.
                    return ASYNC_WOULD_BLOCK;
                };
                if result == ASYNC_UNKNOWN {
                    owner.accepting = false;
                    owner.telemetry.unknown_transitions += 1;
                    owner.slots[slot_index].state = SlotState::Unknown;
                    return ASYNC_UNKNOWN;
                }
                if result == ASYNC_RETIRED {
                    owner.slots[slot_index].state = SlotState::Completed;
                }
                return ASYNC_WOULD_BLOCK;
            };
            let token = alloc_handle();
            if token <= 0 {
                owner.accepting = false;
                return ASYNC_UNKNOWN;
            }
            let slot = &mut owner.slots[index];
            slot.token = token;
            slot.offered_ns = monotonic_ns();
            slot.command = 0;
            slot.state = SlotState::Recording;
            let in_flight = owner.in_flight();
            owner.max_in_flight = owner.max_in_flight.max(in_flight);
            (token, owner.device.clone())
        };
        let command = begin_session_command(&command_owner);
        if command == 0 {
            reset_recording_slot(session, token);
            return ASYNC_INVALID;
        }
        let mut sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get_mut(&session) else {
            drop(sessions);
            discard_recording_command(&command_owner, command);
            return ASYNC_UNKNOWN;
        };
        let Some(slot) = owner
            .slots
            .iter_mut()
            .find(|slot| slot.token == token && slot.state == SlotState::Recording && slot.command == 0)
        else {
            drop(sessions);
            discard_recording_command(&command_owner, command);
            return ASYNC_UNKNOWN;
        };
        slot.command = command;
        token
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        ASYNC_INVALID
    }
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_command(session: i64, token: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get(&session) else {
            return ASYNC_INVALID;
        };
        owner
            .slots
            .iter()
            .find(|slot| slot.token == token && slot.state == SlotState::Recording)
            .map(|slot| slot.command)
            .unwrap_or(ASYNC_INVALID)
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (session, token);
        ASYNC_INVALID
    }
}

fn session_submit_impl(session: i64, token: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let (command, device_identity, sequence) = {
            let mut sessions = ASYNC_SESSIONS.lock();
            let Some(owner) = sessions.get_mut(&session) else {
                return ASYNC_INVALID;
            };
            if !owner.accepting || owner.next_sequence <= 0 || owner.next_sequence == i64::MAX {
                owner.accepting = false;
                return ASYNC_CLOSED;
            }
            let Some(slot) = owner
                .slots
                .iter_mut()
                .find(|slot| slot.token == token && slot.state == SlotState::Recording && slot.command > 0)
            else {
                return ASYNC_INVALID;
            };
            slot.state = SlotState::Submitting;
            (slot.command, owner.device_identity, owner.next_sequence)
        };
        let mut state = STATE.lock();
        let Some(device) = state.device.clone() else {
            drop(state);
            reset_recording_slot(session, token);
            return ASYNC_INVALID;
        };
        if Arc::as_ptr(&device) as usize as u64 != device_identity {
            drop(state);
            reset_recording_slot(session, token);
            return ASYNC_INVALID;
        }
        if !state.compute_commands.contains_key(&command) {
            drop(state);
            reset_recording_slot(session, token);
            return ASYNC_INVALID;
        }
        let owners = state.compute_commands.remove(&command).unwrap_or_default();
        let retained_bytes = owners
            .buffers
            .iter()
            .fold(0i64, |sum, b| sum.saturating_add(b.size().min(i64::MAX as u64) as i64));
        // Reserve the name before queue acceptance. Exhaustion must not create
        // accepted work without a resolvable fence identity.
        let handle = alloc_handle();
        if handle <= 0 {
            device.free_compute_command(vk::CommandBuffer::from_raw(command as u64));
            drop(owners);
            state.set_error("async_session_submit: fence handle allocation exhausted".to_string());
            drop(state);
            reset_recording_slot(session, token);
            return ASYNC_INVALID;
        }
        let fence = match Fence::new(device.clone(), false) {
            Ok(fence) => Arc::new(fence),
            Err(error) => {
                device.free_compute_command(vk::CommandBuffer::from_raw(command as u64));
                drop(owners);
                state.set_error(format!("async_session_submit fence: {error}"));
                drop(state);
                reset_recording_slot(session, token);
                return 0;
            }
        };
        let command_buffer = vk::CommandBuffer::from_raw(command as u64);
        // Declare retained lease bytes before queue acceptance; release accounting
        // happens on explicit retirement or unsubmitted failure.
        drop(state);
        if let Some(owner) = ASYNC_SESSIONS.lock().get_mut(&session) {
            owner.telemetry.retained_bytes = owner.telemetry.retained_bytes.saturating_add(retained_bytes);
            if let Some(slot) = owner.slots.iter_mut().find(|s| s.token == token) {
                slot.retained_bytes = retained_bytes;
            }
            let live = owner
                .slots
                .iter()
                .fold(0i64, |sum, s| sum.saturating_add(s.retained_bytes));
            owner.telemetry.peak_retained_bytes = owner.telemetry.peak_retained_bytes.max(live);
        }
        let mut state = STATE.lock();
        match device.submit_compute_command_no_wait(command_buffer, &fence) {
            Ok(()) => {
                state.accepted_compute_submit_count = state.accepted_compute_submit_count.saturating_add(1);
                state.quarantined_compute.push(QuarantinedComputeSubmission {
                    device,
                    fence,
                    command_buffer,
                    owners,
                    wait_handle: handle,
                });
                state.async_compute_session_fences.insert(handle);
                drop(state);
                let mut sessions = ASYNC_SESSIONS.lock();
                let Some(owner) = sessions.get_mut(&session) else {
                    return ASYNC_UNKNOWN;
                };
                let Some(slot) = owner.slots.iter_mut().find(|slot| slot.token == token && token > 0) else {
                    owner.accepting = false;
                    return ASYNC_UNKNOWN;
                };
                owner.telemetry.accepted = owner.telemetry.accepted.saturating_add(1);
                slot.fence = handle;
                slot.sequence = sequence;
                owner.next_sequence = sequence + 1;
                slot.state = SlotState::Submitted;
                return handle;
            }
            Err(FencedSubmitError::NotSubmitted(error)) => {
                drop(owners);
                state.set_error(format!("async_session_submit: {error}"));
                drop(state);
                reset_recording_slot(session, token);
                return 0;
            }
            Err(FencedSubmitError::CompletionUnknown(error)) => {
                state.quarantined_compute.push(QuarantinedComputeSubmission {
                    device,
                    fence,
                    command_buffer,
                    owners,
                    wait_handle: 0,
                });
                state.set_error(format!("async_session_submit completion unknown: {error}"));
                drop(state);
                if let Some(owner) = ASYNC_SESSIONS.lock().get_mut(&session) {
                    owner.telemetry.unknown_transitions += 1;
                    owner.telemetry.ambiguous = owner.telemetry.ambiguous.saturating_add(1);
                    owner.accepting = false;
                    if let Some(slot) = owner.slots.iter_mut().find(|slot| slot.token == token) {
                        slot.sequence = sequence;
                        slot.state = SlotState::Unknown;
                    }
                    owner.next_sequence = sequence + 1;
                }
                return ASYNC_UNKNOWN;
            }
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (session, token);
        ASYNC_INVALID
    }
}
