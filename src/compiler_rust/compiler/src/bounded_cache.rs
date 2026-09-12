//! Retention-bounded thread-local memo with a borrow-safe eviction policy.
//!
//! The seed interpreter's loader memos (`module_cache::PARSED_SOURCE_CACHE`,
//! `PROBE_SOURCE_CACHE`, `PATH_KEY_CACHE`) were plain `HashMap`s that only ever
//! grew: one process that walks a large import graph retains every source
//! string and every parsed AST until exit, and nothing in the tree could ever
//! give a byte back. This type is the retention bound for exactly those memos —
//! pure, recomputable lookups whose entries can be dropped and rebuilt
//! byte-identically.
//!
//! Three properties are load-bearing and are what the tests pin:
//!
//! 1. **An entry that is currently borrowed is never evicted.** Every value
//!    handed out is a clone whose payload is `Arc`-shared with the cached copy,
//!    so "somebody outside the cache still holds this" is decidable from the
//!    strong count. The pin predicate is supplied per cache
//!    (`fn(&V) -> bool`) rather than through a trait, because the value types
//!    are foreign (`Option<Arc<String>>`, tuples) and an orphan-rule newtype
//!    for each would be machinery for nothing.
//! 2. **A failed release leaves the entry retained and counted.** When the only
//!    over-limit candidates are pinned, the cache stays over its limit rather
//!    than dropping a live entry, and bumps `pinned_skips`. Over-retention is a
//!    recoverable cost; evicting a borrowed entry would be a dangling read.
//! 3. **Eviction is invisible to results.** Entries are pure memos, so an
//!    evicted key is simply refilled by its owner on the next miss.
//!
//! Recency is an approximate LRU: a monotonic tick stamped on every hit and
//! fill, kept in a `Cell` so a lookup needs only `RefCell::borrow()` — these
//! are hot paths and a `borrow_mut()` per read would both cost more and risk a
//! re-entrancy panic.

use std::cell::Cell;
use std::collections::HashMap;
use std::hash::Hash;

/// Counters a caller mirrors into `perf_counters` (process-global atomics are
/// useless to cargo tests, which run in parallel in one process).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CacheStats {
    /// Entries dropped to stay at or under the limit.
    pub evictions: u64,
    /// Times enforcement stopped early because every remaining candidate was
    /// borrowed. Counts enforcement passes, not entries: one pass that could
    /// free nothing is one skip.
    pub pinned_skips: u64,
    /// High-water entry count, sampled after every enforcement pass — so it is
    /// what the cache actually kept, not the transient `limit + 1` that exists
    /// between a fill and its eviction. It exceeds the limit exactly when a
    /// pass could free nothing, which is the over-retention property 2
    /// describes and the reason this is worth reporting at all.
    pub retained_max: usize,
}

struct Entry<V> {
    value: V,
    used: Cell<u64>,
}

/// A `HashMap` memo with an entry-count limit and a borrow-safe eviction pass.
///
/// `limit == 0` means unbounded, which is the pre-bound behaviour and the
/// documented escape hatch for the `SIMPLE_*_CACHE_MAX=0` env overrides.
pub struct BoundedCache<K, V> {
    map: HashMap<K, Entry<V>>,
    tick: Cell<u64>,
    limit: usize,
    pinned: fn(&V) -> bool,
    stats: CacheStats,
}

impl<K: Eq + Hash + Clone, V: Clone> BoundedCache<K, V> {
    /// `pinned` answers "is this value still borrowed by someone outside the
    /// cache?". Pass `|_| false` for a value type that is handed out by copy
    /// and therefore can never be borrowed.
    pub fn new(limit: usize, pinned: fn(&V) -> bool) -> Self {
        Self {
            map: HashMap::new(),
            tick: Cell::new(0),
            limit,
            pinned,
            stats: CacheStats::default(),
        }
    }

    fn next_tick(&self) -> u64 {
        let t = self.tick.get().wrapping_add(1);
        self.tick.set(t);
        t
    }

    /// Lookup. Takes `&self` so hot callers stay on `RefCell::borrow()`.
    pub fn get(&self, key: &K) -> Option<V> {
        let entry = self.map.get(key)?;
        entry.used.set(self.next_tick());
        Some(entry.value.clone())
    }

    /// Fill, then enforce the bound. Returns the stats delta caused by this
    /// insert so the caller can mirror it into process counters without
    /// re-reading the whole struct.
    pub fn insert(&mut self, key: K, value: V) -> CacheStats {
        let used = Cell::new(self.next_tick());
        self.map.insert(key, Entry { value, used });
        let before = self.stats;
        self.enforce_bound();
        CacheStats {
            evictions: self.stats.evictions - before.evictions,
            pinned_skips: self.stats.pinned_skips - before.pinned_skips,
            retained_max: self.stats.retained_max,
        }
    }

    /// Drop least-recently-used entries until at or under the limit, never
    /// dropping one that is still borrowed.
    fn enforce_bound(&mut self) {
        if self.limit > 0 {
            while self.map.len() > self.limit {
                let victim = self
                    .map
                    .iter()
                    .filter(|(_, e)| !(self.pinned)(&e.value))
                    .min_by_key(|(_, e)| e.used.get())
                    .map(|(k, _)| k.clone());
                match victim {
                    Some(key) => {
                        self.map.remove(&key);
                        self.stats.evictions += 1;
                    }
                    // Every over-limit candidate is borrowed. Stay over the
                    // limit: a retained entry costs memory, a freed borrowed
                    // one is a dangling read.
                    None => {
                        self.stats.pinned_skips += 1;
                        break;
                    }
                }
            }
        }
        if self.map.len() > self.stats.retained_max {
            self.stats.retained_max = self.map.len();
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Selective clear, mirroring `HashMap::retain`. Callers use it to drop
    /// entries a *different* invariant has made stale; it is unrelated to the
    /// retention bound, so it neither counts evictions nor enforces the limit
    /// (it only ever shrinks the map).
    pub fn retain<F>(&mut self, mut keep: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.map.retain(|k, e| keep(k, &mut e.value));
    }

    pub fn stats(&self) -> CacheStats {
        self.stats
    }

    pub fn limit(&self) -> usize {
        self.limit
    }

    /// Programmatic limit override. Cargo tests must not depend on env vars:
    /// the env-derived defaults are latched in a process-global `OnceLock`, so
    /// a test that set one would be ignored whenever another test ran first.
    pub fn set_limit(&mut self, limit: usize) {
        self.limit = limit;
        self.enforce_bound();
    }
}

/// Read a `usize` retention limit from `var`, falling back to `default`.
/// An unparseable value falls back too — a bound is a safety property, and a
/// typo in an env var must not silently remove it. `0` means unbounded.
pub fn limit_from_env(var: &str, default: usize) -> usize {
    std::env::var(var)
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .unwrap_or(default)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn arc_pinned(v: &Arc<String>) -> bool {
        Arc::strong_count(v) > 1
    }

    #[test]
    fn fills_past_the_bound_are_evicted_and_counted() {
        let mut cache: BoundedCache<u32, u32> = BoundedCache::new(4, |_| false);
        for i in 0..10u32 {
            cache.insert(i, i * 10);
        }
        assert_eq!(cache.len(), 4, "cache must not exceed its limit");
        assert_eq!(cache.stats().evictions, 6, "every drop past the bound is counted");
        assert_eq!(cache.stats().pinned_skips, 0);
        assert_eq!(
            cache.stats().retained_max,
            4,
            "high-water is what was KEPT, sampled after enforcement, not the transient limit+1"
        );
    }

    #[test]
    fn eviction_is_least_recently_used() {
        let mut cache: BoundedCache<u32, u32> = BoundedCache::new(2, |_| false);
        cache.insert(1, 1);
        cache.insert(2, 2);
        // Touch 1 so 2 becomes the least recently used.
        assert_eq!(cache.get(&1), Some(1));
        cache.insert(3, 3);
        assert_eq!(cache.get(&1), Some(1), "recently used entry survives");
        assert_eq!(cache.get(&2), None, "least recently used entry is the victim");
        assert_eq!(cache.get(&3), Some(3));
    }

    #[test]
    fn a_borrowed_entry_is_skipped_even_when_it_is_the_lru_victim() {
        let mut cache: BoundedCache<u32, Arc<String>> = BoundedCache::new(1, arc_pinned);
        cache.insert(1, Arc::new("borrowed".to_string()));
        // Hold it the way a caller holds a `SharedSource` clone. It is now both
        // pinned AND the least-recently-used entry, so an LRU policy that did
        // not consult the pin predicate would pick exactly this one.
        let borrow = cache.get(&1).expect("filled");
        cache.insert(2, Arc::new("newer".to_string()));

        assert_eq!(
            cache.get(&1).as_deref().map(String::as_str),
            Some("borrowed"),
            "the borrowed entry must survive"
        );
        assert_eq!(&*borrow, "borrowed");
        assert_eq!(cache.stats().evictions, 1, "the unpinned entry is the victim instead");

        // Once the borrow is released the pinned entry becomes evictable.
        drop(borrow);
        let before = cache.stats().evictions;
        cache.insert(3, Arc::new("third".to_string()));
        cache.insert(4, Arc::new("fourth".to_string()));
        assert!(
            cache.stats().evictions > before,
            "releasing the borrow must let enforcement make progress"
        );
        assert!(cache.len() <= 1, "back at the limit once nothing is pinned");
    }

    #[test]
    fn an_all_pinned_cache_stays_over_its_limit_and_counts_the_failed_release() {
        let mut cache: BoundedCache<u32, Arc<String>> = BoundedCache::new(1, arc_pinned);
        // Both entries are held by the caller, exactly as `shared_source` holds
        // the entry it is about to return across its own insert.
        let a = Arc::new("a".to_string());
        let b = Arc::new("b".to_string());
        cache.insert(1, Arc::clone(&a));
        cache.insert(2, Arc::clone(&b));

        assert_eq!(cache.len(), 2, "over-limit rather than free a live entry");
        assert_eq!(cache.stats().evictions, 0, "nothing may be dropped while borrowed");
        assert_eq!(cache.stats().pinned_skips, 1, "the failed release is counted");
        assert_eq!(
            cache.stats().retained_max,
            2,
            "the high-water records that the limit was exceeded"
        );
        assert_eq!(cache.get(&1).as_deref().map(String::as_str), Some("a"));
        assert_eq!(cache.get(&2).as_deref().map(String::as_str), Some("b"));

        drop(a);
        drop(b);
        cache.insert(3, Arc::new("c".to_string()));
        assert!(cache.stats().evictions >= 1, "released entries are reclaimed later");
    }

    #[test]
    fn values_are_byte_identical_after_eviction_and_reload() {
        let rebuild = |i: u32| Arc::new(format!("module-{i}-body"));
        let mut cache: BoundedCache<u32, Arc<String>> = BoundedCache::new(2, arc_pinned);
        for i in 0..6u32 {
            cache.insert(i, rebuild(i));
        }
        assert!(cache.stats().evictions > 0, "the fixture must actually evict");
        for i in 0..6u32 {
            let value = match cache.get(&i) {
                Some(v) => v,
                None => {
                    let v = rebuild(i);
                    cache.insert(i, v.clone());
                    v
                }
            };
            assert_eq!(&*value, &*rebuild(i), "reload must be byte-identical to the first fill");
        }
    }

    #[test]
    fn limit_zero_is_unbounded() {
        let mut cache: BoundedCache<u32, u32> = BoundedCache::new(0, |_| false);
        for i in 0..64u32 {
            cache.insert(i, i);
        }
        assert_eq!(cache.len(), 64);
        assert_eq!(cache.stats().evictions, 0);
        assert_eq!(cache.stats().retained_max, 64);
    }

    #[test]
    fn set_limit_enforces_immediately() {
        let mut cache: BoundedCache<u32, u32> = BoundedCache::new(0, |_| false);
        for i in 0..10u32 {
            cache.insert(i, i);
        }
        cache.set_limit(3);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.stats().evictions, 7);
    }

    #[test]
    fn insert_returns_the_delta_not_the_total() {
        let mut cache: BoundedCache<u32, u32> = BoundedCache::new(1, |_| false);
        cache.insert(1, 1);
        let first = cache.insert(2, 2);
        let second = cache.insert(3, 3);
        assert_eq!(first.evictions, 1);
        assert_eq!(second.evictions, 1, "delta, not the running total");
        assert_eq!(cache.stats().evictions, 2);
    }

    #[test]
    fn limit_from_env_falls_back_on_a_typo() {
        let var = "SIMPLE_L4_BOUNDED_CACHE_TEST_LIMIT";
        std::env::set_var(var, "not-a-number");
        assert_eq!(limit_from_env(var, 77), 77, "a typo must not remove the bound");
        std::env::set_var(var, "5");
        assert_eq!(limit_from_env(var, 77), 5);
        std::env::remove_var(var);
        assert_eq!(limit_from_env(var, 77), 77);
    }
}
