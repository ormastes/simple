fn session_poll_impl(session: i64, token: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let fence = {
            let sessions = ASYNC_SESSIONS.lock();
            let Some(owner) = sessions.get(&session) else {
                return ASYNC_INVALID;
            };
            let Some(slot) = owner.slots.iter().find(|slot| slot.token == token && slot.token > 0) else {
                return ASYNC_INVALID;
            };
            match slot.state {
                SlotState::Unknown => return ASYNC_UNKNOWN,
                SlotState::Completed => return ASYNC_RETIRED,
                SlotState::Submitted => slot.fence,
                _ => return ASYNC_INVALID,
            }
        };
        let result = poll_fence(fence);
        let mut sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get_mut(&session) else {
            return ASYNC_INVALID;
        };
        let Some(slot) = owner
            .slots
            .iter_mut()
            .find(|slot| slot.token == token && slot.fence == fence && slot.state == SlotState::Submitted)
        else {
            return ASYNC_INVALID;
        };
        if result == ASYNC_RETIRED {
            slot.state = SlotState::Completed;
        } else if result == ASYNC_UNKNOWN {
            slot.state = SlotState::Unknown;
            owner.telemetry.unknown_transitions += 1;
            owner.accepting = false;
        }
        result
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (session, token);
        ASYNC_INVALID
    }
}

fn session_retire_impl(session: i64, token: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let (fence, sequence) = {
            let mut sessions = ASYNC_SESSIONS.lock();
            let Some(owner) = sessions.get_mut(&session) else {
                return ASYNC_INVALID;
            };
            let Some(slot) = owner.slots.iter_mut().find(|slot| slot.token == token) else {
                return ASYNC_INVALID;
            };
            match slot.state {
                SlotState::Submitted => return ASYNC_PENDING,
                SlotState::Unknown => return ASYNC_UNKNOWN,
                SlotState::Completed => {}
                SlotState::Free | SlotState::Recording | SlotState::Submitting | SlotState::Retiring => {
                    return ASYNC_INVALID
                }
            }
            slot.state = SlotState::Retiring;
            (slot.fence, slot.sequence)
        };
        let result = retire_fence(fence);
        let mut sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get_mut(&session) else {
            return ASYNC_UNKNOWN;
        };
        let Some(slot_index) = owner.slots.iter().position(|slot| slot.token == token) else {
            return ASYNC_INVALID;
        };
        if result == ASYNC_RETIRED {
            owner.telemetry.released_bytes = owner
                .telemetry
                .released_bytes
                .saturating_add(owner.slots[slot_index].retained_bytes);
            owner.telemetry.latencies[Metric::Frame as usize]
                .record(monotonic_ns().saturating_sub(owner.slots[slot_index].offered_ns));
            owner.publish(sequence);
            if !owner.slots[slot_index].reset_for_reuse() {
                owner.accepting = false;
            }
        } else if result == ASYNC_PENDING {
            owner.slots[slot_index].state = SlotState::Completed;
        } else {
            owner.accepting = false;
            owner.slots[slot_index].state = SlotState::Unknown;
        }
        result
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (session, token);
        ASYNC_INVALID
    }
}
