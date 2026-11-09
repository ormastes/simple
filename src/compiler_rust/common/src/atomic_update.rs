//! Conditional atomic updates compatible with bootstrap toolchains predating
//! `Atomic::try_update`. Keep the same retry and ordering contract without using
//! the deprecated `fetch_update` name.

use std::sync::atomic::{AtomicI64, AtomicU32, AtomicUsize, Ordering};

macro_rules! conditional_update {
    ($name:ident, $atomic:ty, $value:ty) => {
        /// Return the previous value on success, or the observed value when the
        /// callback declines an update. The callback may run repeatedly under
        /// contention; failure ordering also governs the initial load.
        pub fn $name<F>(atomic: &$atomic, success: Ordering, failure: Ordering, mut update: F) -> Result<$value, $value>
        where
            F: FnMut($value) -> Option<$value>,
        {
            let mut current = atomic.load(failure);
            loop {
                let Some(next) = update(current) else {
                    return Err(current);
                };
                match atomic.compare_exchange_weak(current, next, success, failure) {
                    Ok(previous) => return Ok(previous),
                    Err(observed) => current = observed,
                }
            }
        }
    };
}

conditional_update!(update_i64, AtomicI64, i64);
conditional_update!(update_u32, AtomicU32, u32);
conditional_update!(update_usize, AtomicUsize, usize);

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};

    #[test]
    fn checked_boundaries_leave_exhausted_counters_unchanged() {
        let counter = AtomicI64::new(i64::MAX - 1);
        assert_eq!(
            update_i64(&counter, Ordering::SeqCst, Ordering::SeqCst, |n| n.checked_add(1)),
            Ok(i64::MAX - 1)
        );
        assert_eq!(
            update_i64(&counter, Ordering::SeqCst, Ordering::SeqCst, |n| n.checked_add(1)),
            Err(i64::MAX)
        );
        assert_eq!(counter.load(Ordering::SeqCst), i64::MAX);
        let depth = AtomicUsize::new(1);
        assert_eq!(
            update_usize(&depth, Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_sub(1)),
            Ok(1)
        );
        assert_eq!(
            update_usize(&depth, Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_sub(1)),
            Err(0)
        );
        assert_eq!(depth.load(Ordering::Relaxed), 0);
        let scope = AtomicU32::new(u32::MAX);
        let next_scope = |n: u32| {
            if n == 0 {
                None
            } else {
                Some(n.checked_add(1).unwrap_or(0))
            }
        };
        assert_eq!(
            update_u32(&scope, Ordering::Relaxed, Ordering::Relaxed, next_scope),
            Ok(u32::MAX)
        );
        assert_eq!(
            update_u32(&scope, Ordering::Relaxed, Ordering::Relaxed, next_scope),
            Err(0)
        );
    }

    #[test]
    fn retries_callback_with_observed_value_and_can_decline_after_race() {
        let counter = AtomicI64::new(4);
        let mut calls = Vec::new();
        let result = update_i64(&counter, Ordering::AcqRel, Ordering::Acquire, |n| {
            calls.push(n);
            if n == 4 {
                counter.store(9, Ordering::Release);
                Some(5)
            } else {
                None
            }
        });
        assert_eq!(result, Err(9));
        assert_eq!(calls, vec![4, 9]);
        assert_eq!(counter.load(Ordering::Acquire), 9);
    }

    #[test]
    fn concurrent_allocations_are_unique_and_stop_at_exhaustion() {
        let counter = Arc::new(AtomicI64::new(i64::MAX - 512));
        let barrier = Arc::new(Barrier::new(8));
        let mut threads = Vec::new();
        for _ in 0..8 {
            let counter = Arc::clone(&counter);
            let barrier = Arc::clone(&barrier);
            threads.push(std::thread::spawn(move || {
                barrier.wait();
                let mut handles = Vec::new();
                while let Ok(handle) = update_i64(&counter, Ordering::SeqCst, Ordering::SeqCst, |n| n.checked_add(1)) {
                    handles.push(handle);
                }
                handles
            }));
        }
        let mut handles: Vec<_> = threads.into_iter().flat_map(|thread| thread.join().unwrap()).collect();
        handles.sort_unstable();
        assert_eq!(handles, ((i64::MAX - 512)..i64::MAX).collect::<Vec<_>>());
        assert_eq!(counter.load(Ordering::SeqCst), i64::MAX);
    }
}
