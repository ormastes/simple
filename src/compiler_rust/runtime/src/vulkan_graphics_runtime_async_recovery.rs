// Recovery is explicit and never part of acquire/submit/poll/retire. Unknown
// completion remains owned until idle proves release safe, or the entire device
// generation is detached into a bounded process-lifetime quarantine.
#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    static ref ASYNC_QUARANTINED_DEVICE: Mutex<Option<super::vulkan_graphics_runtime_core::VulkanState>> = Mutex::new(None);
}

/// Close admission and attempt ONE device-idle recovery outside registry locks.
/// Success resolves physical ownership but never manufactures frame receipts
/// for ambiguous submissions. The caller may inspect telemetry then close.
#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_recover(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let _operation = ASYNC_OPERATION_GATE.lock();
        let device = {
            let mut sessions = ASYNC_SESSIONS.lock();
            let Some(owner) = sessions.get_mut(&session) else {
                return ASYNC_INVALID;
            };
            owner.accepting = false;
            owner.telemetry.recovery_attempts += 1;
            owner.device.clone()
        };
        if let Err(error) = device.wait_idle() {
            STATE.lock().set_error(format!("async_session_recover: {error}"));
            return ASYNC_UNKNOWN;
        }
        let commands = {
            let sessions = ASYNC_SESSIONS.lock();
            let owner = sessions.get(&session).unwrap();
            owner
                .slots
                .iter()
                .filter(|slot| slot.command > 0)
                .map(|slot| slot.command)
                .collect::<Vec<_>>()
        };
        {
            let mut state = STATE.lock();
            if !state.device.as_ref().is_some_and(|active| Arc::ptr_eq(active, &device)) {
                return ASYNC_UNKNOWN;
            }
            // One session owns this direct-compute generation. Do not touch
            // unrelated graphics work or manufacture caller fence tombstones.
            let mut index = 0;
            while index < state.quarantined_compute.len() {
                if commands.contains(&(state.quarantined_compute[index].command_buffer.as_raw() as i64)) {
                    let entry = state.quarantined_compute.swap_remove(index);
                    state.async_compute_session_fences.remove(&entry.wait_handle);
                    device.free_compute_command(entry.command_buffer);
                    drop(entry);
                } else {
                    index += 1;
                }
            }
            for command in commands {
                if state.compute_commands.remove(&command).is_some() {
                    device.free_compute_command(vk::CommandBuffer::from_raw(command as u64));
                }
            }
        }
        let mut sessions = ASYNC_SESSIONS.lock();
        let owner = sessions.get_mut(&session).unwrap();
        for slot in &mut owner.slots {
            owner.telemetry.released_bytes = owner.telemetry.released_bytes.saturating_add(slot.retained_bytes);
            // Admission stays closed. Exhausted slot generations are never
            // reused, but physical ownership has still been resolved.
            let _ = slot.reset_for_reuse();
        }
        owner.retired_sequences.clear();
        owner.telemetry.recoveries += 1;
        return ASYNC_RETIRED;
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        ASYNC_INVALID
    }
}

/// Explicit forced teardown after failed recovery. This revokes every public
/// handle in the affected device generation atomically. It retains ALL runtime
/// objects, not merely the async fence, because the driver may still access
/// them. Quarantine has one fixed slot; a second unresolved device is rejected.
/// The process must restart before another device generation can initialize.
/// Return 2 means quarantined, never "GPU completed" or "resources released".
#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_abandon_device(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let _operation = ASYNC_OPERATION_GATE.lock();
        let mut sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get_mut(&session) else {
            return ASYNC_INVALID;
        };
        if owner.accepting || owner.telemetry.recovery_attempts == owner.telemetry.recoveries {
            return ASYNC_INVALID;
        }
        let mut quarantine = ASYNC_QUARANTINED_DEVICE.lock();
        if quarantine.is_some() {
            return ASYNC_WOULD_BLOCK;
        }
        let mut state = STATE.lock();
        if !state
            .device
            .as_ref()
            .is_some_and(|active| Arc::ptr_eq(active, &owner.device))
        {
            return ASYNC_INVALID;
        }
        owner.accepting = false;
        owner.telemetry.quarantined = 1;
        let retained = std::mem::replace(&mut *state, super::vulkan_graphics_runtime_core::VulkanState::new());
        state.device_generation_quarantined = true;
        *quarantine = Some(retained);
        // Keep a terminal scalar snapshot: outstanding owner and byte counts
        // remain nonzero and completion receipts remain unpublished.
        let words = owner.telemetry_words();
        *ASYNC_LAST_CLOSED.lock() = Some((session, words));
        sessions.remove(&session);
        return ASYNC_QUARANTINED;
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        ASYNC_INVALID
    }
}
