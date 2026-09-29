#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_receipt(session: i64, sequence: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        ASYNC_SESSIONS
            .lock()
            .get(&session)
            .map(|owner| i64::from(sequence > 0 && sequence <= owner.published_sequence))
            .unwrap_or(0)
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (session, sequence);
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_cancel(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let _operation = ASYNC_OPERATION_GATE.lock();
        let mut sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get_mut(&session) else {
            return ASYNC_INVALID;
        };
        if owner.accepting {
            owner.telemetry.cancellations += 1;
        }
        owner.accepting = false;
        return 1;
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        ASYNC_INVALID
    }
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_close(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let _operation = ASYNC_OPERATION_GATE.lock();
        let mut sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get_mut(&session) else {
            return 1;
        };
        owner.accepting = false;
        let recording: Vec<(i64, i64)> = owner
            .slots
            .iter_mut()
            .filter(|slot| slot.state == SlotState::Recording)
            .map(|slot| {
                slot.state = SlotState::Submitting;
                (slot.token, slot.command)
            })
            .collect();
        let device = owner.device.clone();
        drop(sessions);
        for (_, command) in &recording {
            discard_recording_command(&device, *command);
        }
        let mut sessions = ASYNC_SESSIONS.lock();
        let Some(owner) = sessions.get_mut(&session) else {
            return 1;
        };
        for (token, _) in recording {
            if let Some(slot) = owner
                .slots
                .iter_mut()
                .find(|slot| slot.token == token && slot.state == SlotState::Submitting)
            {
                if !slot.reset_for_reuse() {
                    owner.accepting = false;
                }
            }
        }
        if owner.in_flight() != 0 {
            if owner.slots.iter().any(|slot| slot.state == SlotState::Unknown) {
                return ASYNC_UNKNOWN;
            }
            return 0;
        }
        let mut owner = sessions.remove(&session).unwrap();
        owner.snapshot = owner.telemetry_words();
        owner.snapshot[4] = 0;
        *ASYNC_LAST_CLOSED.lock() = Some((session, owner.snapshot));
        drop(sessions);
        STATE.lock().async_compute_session_active = false;
        return 1;
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_capacity(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        return ASYNC_SESSIONS
            .lock()
            .get(&session)
            .map(|s| s.capacity as i64)
            .unwrap_or(0);
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_in_flight(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        return ASYNC_SESSIONS
            .lock()
            .get(&session)
            .map(AsyncSession::in_flight)
            .unwrap_or(-1);
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        -1
    }
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_published_sequence(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        return ASYNC_SESSIONS
            .lock()
            .get(&session)
            .map(|s| s.published_sequence)
            .unwrap_or(-1);
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = session;
        -1
    }
}
