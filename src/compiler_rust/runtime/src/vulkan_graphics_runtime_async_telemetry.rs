// Bounded host telemetry. Every snapshot is a copied, versioned scalar record;
// publishing another snapshot invalidates the older token rather than mixing
// values from different observations.
const TELEMETRY_WORDS: usize = 64;

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    static ref ASYNC_CLOCK: Instant = Instant::now();
    static ref ASYNC_LAST_CLOSED: Mutex<Option<(i64, [i64; TELEMETRY_WORDS])>> = Mutex::new(None);
    static ref ASYNC_TERMINAL_SNAPSHOT: Mutex<Option<(i64, i64, [i64; TELEMETRY_WORDS])>> = Mutex::new(None);
}

#[cfg(feature = "vulkan")]
fn monotonic_ns() -> i64 {
    ASYNC_CLOCK.elapsed().as_nanos().min(i64::MAX as u128) as i64
}

#[cfg(feature = "vulkan")]
fn elapsed_ns(start: Instant) -> i64 {
    start.elapsed().as_nanos().min(i64::MAX as u128) as i64
}

#[cfg(feature = "vulkan")]
impl AsyncSession {
    fn telemetry_words(&self) -> [i64; TELEMETRY_WORDS] {
        let mut words = [0; TELEMETRY_WORDS];
        words[..24].copy_from_slice(&[
            1,
            TELEMETRY_WORDS as i64,
            monotonic_ns(),
            self.capacity as i64,
            self.in_flight(),
            self.max_in_flight,
            i64::from(self.accepting),
            self.telemetry.attempted,
            self.telemetry.accepted,
            self.telemetry.rejected,
            self.telemetry.ambiguous,
            self.telemetry.polls,
            self.telemetry.poll_pending,
            self.telemetry.poll_complete,
            self.telemetry.poll_failed,
            self.bounded_waits,
            self.backpressure_events,
            self.telemetry.retirements,
            self.telemetry.cancellations,
            self.telemetry.retained_bytes,
            self.telemetry.released_bytes,
            self.telemetry.recovery_attempts,
            self.telemetry.recoveries,
            self.published_sequence,
        ]);
        // Zero means unavailable, never a fabricated GPU timestamp.
        words[24] = 0;
        words[25] = self.telemetry.quarantined;
        words[26] = self.slots.iter().filter(|s| s.state == SlotState::Unknown).count() as i64;
        words[27] = self
            .slots
            .iter()
            .fold(0i64, |sum, s| sum.saturating_add(s.retained_bytes));
        words[28] = self.wait_timeout_ns as i64;
        words[29] = self.telemetry.unknown_transitions;
        words[30] = i64::from(self.telemetry.quarantined != 0);
        words[31] = self.telemetry.peak_retained_bytes;
        // Each metric: lifetime samples, last ns, total ns, rolling p50, p95.
        // The fixed window is the most recent 64 observations, NOT all frames.
        for (index, latency) in self.telemetry.latencies.iter().enumerate() {
            let base = 32 + index * 5;
            words[base..base + 5].copy_from_slice(&[
                latency.count,
                latency.last,
                latency.total,
                latency.percentile(50),
                latency.percentile(95),
            ]);
        }
        words
    }
}

#[cfg(feature = "vulkan")]
fn record_observation(session: i64, metric: Metric, ns: i64, result: i64) {
    let mut sessions = ASYNC_SESSIONS.lock();
    let Some(owner) = sessions.get_mut(&session) else {
        return;
    };
    owner.telemetry.latencies[metric as usize].record(ns);
    match metric {
        Metric::Offer => {
            owner.telemetry.attempted = owner.telemetry.attempted.saturating_add(1);
            if result <= 0 && result != ASYNC_UNKNOWN {
                owner.telemetry.rejected = owner.telemetry.rejected.saturating_add(1);
            }
        }
        Metric::Poll => {
            owner.telemetry.polls = owner.telemetry.polls.saturating_add(1);
            match result {
                ASYNC_PENDING => owner.telemetry.poll_pending += 1,
                ASYNC_RETIRED => owner.telemetry.poll_complete += 1,
                _ => owner.telemetry.poll_failed += 1,
            }
        }
        Metric::Retire if result == ASYNC_RETIRED => owner.telemetry.retirements += 1,
        _ => {}
    }
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_supported() -> i64 {
    i64::from(cfg!(feature = "vulkan"))
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_acquire(session: i64) -> i64 {
    session_acquire_impl(session)
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_submit(session: i64, token: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    let _operation = ASYNC_OPERATION_GATE.lock();
    #[cfg(feature = "vulkan")]
    let start = Instant::now();
    let result = session_submit_impl(session, token);
    #[cfg(feature = "vulkan")]
    record_observation(session, Metric::Offer, elapsed_ns(start), result);
    result
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_poll(session: i64, token: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    let start = Instant::now();
    let result = session_poll_impl(session, token);
    #[cfg(feature = "vulkan")]
    record_observation(session, Metric::Poll, elapsed_ns(start), result);
    result
}

#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_retire(session: i64, token: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    let _operation = ASYNC_OPERATION_GATE.lock();
    #[cfg(feature = "vulkan")]
    let start = Instant::now();
    let result = session_retire_impl(session, token);
    #[cfg(feature = "vulkan")]
    record_observation(session, Metric::Retire, elapsed_ns(start), result);
    result
}

/// Freeze one versioned record. One snapshot is retained per live session and
/// one terminal record globally; both are bounded and carry no device owner.
#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_snapshot(session: i64) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let mut sessions = ASYNC_SESSIONS.lock();
        if let Some(owner) = sessions.get_mut(&session) {
            let token = alloc_handle();
            if token <= 0 {
                return ASYNC_INVALID;
            }
            owner.snapshot = owner.telemetry_words();
            owner.snapshot_token = token;
            return token;
        }
        let terminal = ASYNC_LAST_CLOSED.lock();
        if let Some((closed, words)) = terminal.as_ref().filter(|(id, _)| *id == session) {
            let token = alloc_handle();
            if token <= 0 {
                return ASYNC_INVALID;
            }
            *ASYNC_TERMINAL_SNAPSHOT.lock() = Some((*closed, token, *words));
            return token;
        }
    }
    let _ = session;
    ASYNC_INVALID
}

/// Reading a replaced, stale or wrong-session snapshot fails explicitly.
#[no_mangle]
pub extern "C" fn rt_vulkan_async_session_snapshot_word(session: i64, snapshot: i64, index: i64) -> i64 {
    if snapshot <= 0 || !(0..TELEMETRY_WORDS as i64).contains(&index) {
        return ASYNC_INVALID;
    }
    #[cfg(feature = "vulkan")]
    {
        let sessions = ASYNC_SESSIONS.lock();
        if let Some(owner) = sessions.get(&session) {
            return if owner.snapshot_token == snapshot {
                owner.snapshot[index as usize]
            } else {
                ASYNC_INVALID
            };
        }
        if let Some((_, _, words)) = ASYNC_TERMINAL_SNAPSHOT
            .lock()
            .as_ref()
            .filter(|(id, token, _)| *id == session && *token == snapshot)
        {
            return words[index as usize];
        }
    }
    let _ = session;
    ASYNC_INVALID
}
