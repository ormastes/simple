use std::collections::HashSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SlotState {
    Free,
    Recording,
    Submitting,
    Submitted,
    Completed,
    Retiring,
    Unknown,
}

pub(crate) struct AsyncSlot {
    pub(crate) generation: u64,
    pub(crate) token: i64,
    pub(crate) command: i64,
    pub(crate) fence: i64,
    pub(crate) sequence: i64,
    pub(crate) offered_ns: i64,
    pub(crate) retained_bytes: i64,
    pub(crate) state: SlotState,
}

impl AsyncSlot {
    pub(crate) fn new() -> Self {
        Self {
            generation: 1,
            token: 0,
            command: 0,
            fence: 0,
            sequence: 0,
            offered_ns: 0,
            retained_bytes: 0,
            state: SlotState::Free,
        }
    }

    pub(crate) fn reset_for_reuse(&mut self) -> bool {
        // Called only after physical release. Clear resolved identities even
        // on exhaustion; the caller closes admission when this returns false.
        let next_generation = self.generation.checked_add(1);
        if let Some(next) = next_generation {
            self.generation = next;
        }
        self.token = 0;
        self.command = 0;
        self.fence = 0;
        self.sequence = 0;
        self.offered_ns = 0;
        self.retained_bytes = 0;
        self.state = SlotState::Free;
        next_generation.is_some()
    }
}

pub(crate) fn publish_contiguous(published: &mut i64, retired: &mut HashSet<i64>, sequence: i64) {
    if sequence <= *published {
        return;
    }
    retired.insert(sequence);
    while let Some(next) = published.checked_add(1) {
        if !retired.remove(&next) {
            break;
        }
        *published = next;
    }
}

#[derive(Clone, Copy)]
pub(crate) enum Metric {
    Offer = 0,
    Poll = 1,
    Wait = 2,
    Retire = 3,
    Frame = 4,
}

#[derive(Clone)]
pub(crate) struct Latency {
    pub(crate) count: i64,
    pub(crate) last: i64,
    pub(crate) total: i64,
    samples: [i64; 64],
    cursor: usize,
}

impl Default for Latency {
    fn default() -> Self {
        Self {
            count: 0,
            last: 0,
            total: 0,
            samples: [0; 64],
            cursor: 0,
        }
    }
}

impl Latency {
    pub(crate) fn record(&mut self, ns: i64) {
        self.last = ns.max(0);
        self.count = self.count.saturating_add(1);
        self.total = self.total.saturating_add(self.last);
        self.samples[self.cursor] = self.last;
        self.cursor = (self.cursor + 1) % self.samples.len();
    }
    pub(crate) fn percentile(&self, percentile: usize) -> i64 {
        let used = self.count.min(self.samples.len() as i64) as usize;
        if used == 0 {
            return 0;
        }
        let mut sorted = self.samples;
        sorted[..used].sort_unstable();
        sorted[(used * percentile.clamp(1, 100)).div_ceil(100) - 1]
    }
}

#[derive(Default)]
pub(crate) struct AsyncTelemetry {
    pub(crate) attempted: i64,
    pub(crate) accepted: i64,
    pub(crate) rejected: i64,
    pub(crate) ambiguous: i64,
    pub(crate) polls: i64,
    pub(crate) poll_pending: i64,
    pub(crate) poll_complete: i64,
    pub(crate) poll_failed: i64,
    pub(crate) retirements: i64,
    pub(crate) cancellations: i64,
    pub(crate) retained_bytes: i64,
    pub(crate) released_bytes: i64,
    pub(crate) recovery_attempts: i64,
    pub(crate) recoveries: i64,
    pub(crate) quarantined: i64,
    pub(crate) unknown_transitions: i64,
    pub(crate) peak_retained_bytes: i64,
    pub(crate) latencies: [Latency; 5],
}

/// Reserve a bounded sequence window as well as physical slot storage.
pub(crate) fn admission_index(slots: &[AsyncSlot], next: i64, published: i64) -> Option<usize> {
    let reserved = slots.iter().filter(|s| s.state == SlotState::Recording).count() as i64;
    if next <= 0
        || published < 0
        || next == i64::MAX
        || next <= published
        || next - published - 1 + reserved >= slots.len() as i64
    {
        return None;
    }
    slots.iter().position(|slot| slot.state == SlotState::Free)
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slot_generation_rejects_exhaustion_instead_of_wrapping() {
        let mut slot = AsyncSlot::new();
        slot.generation = u64::MAX;
        assert!(!slot.reset_for_reuse());
        assert_eq!(slot.state, SlotState::Free);
    }

    #[test]
    fn slot_reuse_invalidates_every_prior_identity_field() {
        let mut slot = AsyncSlot {
            generation: 7,
            token: 11,
            command: 12,
            fence: 13,
            sequence: 14,
            offered_ns: 17,
            retained_bytes: 123,
            state: SlotState::Completed,
        };
        assert!(slot.reset_for_reuse());
        assert_eq!(slot.generation, 8);
        assert_eq!(slot.token, 0);
        assert_eq!(slot.command, 0);
        assert_eq!(slot.fence, 0);
        assert_eq!(slot.sequence, 0);
        assert_eq!(slot.state, SlotState::Free);
    }

    #[test]
    fn receipts_publish_only_the_contiguous_sequence_prefix() {
        let mut published = 0;
        let mut retired = HashSet::new();
        publish_contiguous(&mut published, &mut retired, 2);
        assert_eq!(published, 0);
        publish_contiguous(&mut published, &mut retired, 1);
        assert_eq!(published, 2);
        assert!(retired.is_empty());
    }

    fn slots(capacity: usize) -> Vec<AsyncSlot> {
        (0..capacity).map(|_| AsyncSlot::new()).collect()
    }

    #[test]
    fn selected_capacities_never_grow_and_recording_reserves_space() {
        for capacity in [3, 8, 16] {
            let mut slots = slots(capacity);
            for index in 0..capacity {
                assert_eq!(admission_index(&slots, 1, 0), Some(index));
                slots[index].state = SlotState::Recording;
            }
            assert_eq!(admission_index(&slots, 1, 0), None);
            assert_eq!(slots.len(), capacity);
        }
    }

    #[test]
    fn completion_does_not_release_slot_capacity() {
        for state in [
            SlotState::Submitted,
            SlotState::Completed,
            SlotState::Unknown,
            SlotState::Submitting,
            SlotState::Retiring,
        ] {
            let mut slots = slots(3);
            for slot in &mut slots {
                slot.state = state;
            }
            assert_eq!(admission_index(&slots, 1, 0), None);
        }
    }

    #[test]
    fn recycled_slot_accepts_command_four_after_prefix_retirement() {
        let mut slots = slots(3);
        for (index, slot) in slots.iter_mut().enumerate() {
            slot.state = SlotState::Submitted;
            slot.sequence = index as i64 + 1;
            slot.token = index as i64 + 100;
        }
        assert_eq!(admission_index(&slots, 4, 0), None);
        assert!(slots[0].reset_for_reuse());
        let mut published = 0;
        publish_contiguous(&mut published, &mut HashSet::new(), 1);
        assert_eq!(admission_index(&slots, 4, published), Some(0));
        assert_eq!(slots[0].generation, 2);
        assert!(!slots.iter().any(|slot| slot.token == 100));
    }

    #[test]
    fn stalled_prefix_bounds_retired_receipts_even_with_free_physical_slots() {
        let mut slots = slots(3);
        slots[0].state = SlotState::Submitted;
        slots[0].sequence = 1;
        let mut published = 0;
        let mut retired = HashSet::new();
        publish_contiguous(&mut published, &mut retired, 3);
        publish_contiguous(&mut published, &mut retired, 2);
        assert_eq!(retired.len(), 2);
        assert_eq!(admission_index(&slots, 4, published), None);
        publish_contiguous(&mut published, &mut retired, 1);
        assert_eq!(published, 3);
        assert!(retired.is_empty());
        assert_eq!(admission_index(&slots, 4, published), Some(1));
    }

    #[test]
    fn receipt_publication_is_deterministic_for_every_small_permutation() {
        for a in 1..=3 {
            for b in 1..=3 {
                for c in 1..=3 {
                    if a == b || b == c || a == c {
                        continue;
                    }
                    let mut published = 0;
                    let mut retired = HashSet::new();
                    for value in [a, b, c] {
                        publish_contiguous(&mut published, &mut retired, value);
                        assert!(retired.len() <= 2);
                    }
                    assert_eq!(published, 3);
                    assert!(retired.is_empty());
                }
            }
        }
    }

    #[test]
    fn duplicate_consumed_receipts_do_not_accumulate_tombstones() {
        let mut published = 3;
        let mut retired = HashSet::new();
        for value in [-1, 0, 1, 2, 3, 3] {
            publish_contiguous(&mut published, &mut retired, value);
        }
        assert!(retired.is_empty());
        assert_eq!(published, 3);
    }

    #[test]
    fn exhaustion_clears_already_released_owners_but_never_wraps_generation() {
        let mut slot = AsyncSlot::new();
        slot.generation = u64::MAX;
        slot.token = 42;
        slot.command = 43;
        slot.fence = 44;
        slot.retained_bytes = 1024;
        slot.state = SlotState::Completed;
        assert!(!slot.reset_for_reuse());
        assert_eq!(slot.generation, u64::MAX);
        assert_eq!(
            (slot.token, slot.command, slot.fence, slot.retained_bytes),
            (0, 0, 0, 0)
        );
        assert_eq!(slot.state, SlotState::Free);
    }

    #[test]
    fn admission_rejects_invalid_or_exhausted_sequence_authority() {
        let slots = slots(3);
        for (next, published) in [(0, 0), (-1, 0), (1, -1), (1, 1), (i64::MAX, 0)] {
            assert_eq!(admission_index(&slots, next, published), None);
        }
    }

    #[test]
    fn publication_at_integer_limit_is_checked() {
        let mut published = i64::MAX - 1;
        let mut retired = HashSet::new();
        publish_contiguous(&mut published, &mut retired, i64::MAX);
        assert_eq!(published, i64::MAX);
        assert!(retired.is_empty());
    }

    #[test]
    fn monotonic_latency_uses_bounded_window_and_separate_lifetime_total() {
        let mut latency = Latency::default();
        assert_eq!(latency.percentile(95), 0);
        for ns in 1..=128 {
            latency.record(ns);
        }
        assert_eq!(latency.count, 128);
        assert_eq!(latency.last, 128);
        assert_eq!(latency.total, 8256);
        assert_eq!(latency.percentile(50), 96);
        assert_eq!(latency.percentile(95), 125);
        assert_eq!(latency.samples.len(), 64);
    }

    #[test]
    fn invalid_latency_never_manufactures_negative_time_or_counter_wrap() {
        let mut latency = Latency::default();
        latency.record(-100);
        assert_eq!(latency.last, 0);
        latency.total = i64::MAX;
        latency.count = i64::MAX;
        latency.record(12);
        assert_eq!(latency.total, i64::MAX);
        assert_eq!(latency.count, i64::MAX);
    }
}
