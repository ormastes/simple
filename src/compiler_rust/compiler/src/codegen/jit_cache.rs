//! JIT cache with call-count-triggered compilation.
//!
//! Tracks per-function call counts in the interpreter. When a function exceeds
//! the hot threshold, it is compiled via Cranelift JIT and the native pointer
//! is cached for subsequent invocations — bypassing the interpreter entirely.
//!
//! Architecture rationale ("why Rust, not direct C?"):
//! The Rust layer IS the compiler — it parses Simple source, builds MIR, and
//! emits native code via Cranelift. Static externs (`rt_cuda_memset` etc.) are
//! already direct C calls at the ABI boundary. The overhead is NOT Rust-to-C
//! dispatch; it's the interpreter loop (Value boxing, scope lookup, expression
//! evaluation). JIT compilation eliminates ALL of that for hot paths by emitting
//! native machine code that calls C symbols directly — no interpreter, no boxing.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

/// Default call-count threshold before JIT compilation triggers.
/// Tuned for interactive workloads: low enough to catch hot loops,
/// high enough to avoid compiling one-shot setup functions.
pub const DEFAULT_JIT_THRESHOLD: u64 = 64;

/// Per-function profiling entry.
struct FuncProfile {
    call_count: AtomicU64,
    /// Once compiled, stores the native function pointer.
    /// None = still interpreting, Some = JIT-compiled.
    compiled_ptr: Option<*const u8>,
}

// Safety: compiled_ptr is only written once under lock and read thereafter.
unsafe impl Send for FuncProfile {}
unsafe impl Sync for FuncProfile {}

/// Global JIT cache — shared across interpreter threads.
pub struct JitCache {
    profiles: HashMap<String, FuncProfile>,
    threshold: u64,
    /// Number of functions that have been JIT-compiled.
    compiled_count: u64,
    /// Whether JIT is enabled (can be disabled via env var or flag).
    enabled: bool,
}

impl JitCache {
    pub fn new(threshold: u64) -> Self {
        Self {
            profiles: HashMap::new(),
            threshold,
            compiled_count: 0,
            enabled: true,
        }
    }

    /// Record a call and return whether this function has been JIT-compiled.
    /// Returns Some(ptr) if the function is already compiled, None otherwise.
    /// When call count crosses threshold, returns None but marks the function
    /// as a compilation candidate (caller should trigger async compilation).
    pub fn record_call(&mut self, name: &str) -> CallResult {
        if !self.enabled {
            return CallResult::Interpret;
        }

        let entry = self.profiles.entry(name.to_string()).or_insert_with(|| FuncProfile {
            call_count: AtomicU64::new(0),
            compiled_ptr: None,
        });

        if let Some(ptr) = entry.compiled_ptr {
            return CallResult::Compiled(ptr);
        }

        let count = entry.call_count.fetch_add(1, Ordering::Relaxed) + 1;
        if count >= self.threshold {
            CallResult::CompileNow
        } else {
            CallResult::Interpret
        }
    }

    /// Store a compiled function pointer after JIT compilation succeeds.
    pub fn store_compiled(&mut self, name: &str, ptr: *const u8) {
        if let Some(entry) = self.profiles.get_mut(name) {
            entry.compiled_ptr = Some(ptr);
            self.compiled_count += 1;
        }
    }

    pub fn compiled_count(&self) -> u64 {
        self.compiled_count
    }

    pub fn set_enabled(&mut self, enabled: bool) {
        self.enabled = enabled;
    }

    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Reset all profiles (useful for testing or mode switches).
    pub fn reset(&mut self) {
        self.profiles.clear();
        self.compiled_count = 0;
    }

    /// Get profiling stats: (total_tracked, compiled, hottest_uncompiled).
    pub fn stats(&self) -> JitCacheStats {
        let total = self.profiles.len() as u64;
        let mut hottest_name = String::new();
        let mut hottest_count = 0u64;

        for (name, profile) in &self.profiles {
            if profile.compiled_ptr.is_none() {
                let count = profile.call_count.load(Ordering::Relaxed);
                if count > hottest_count {
                    hottest_count = count;
                    hottest_name = name.clone();
                }
            }
        }

        JitCacheStats {
            total_tracked: total,
            compiled: self.compiled_count,
            threshold: self.threshold,
            hottest_uncompiled: if hottest_count > 0 {
                Some((hottest_name, hottest_count))
            } else {
                None
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct JitCacheStats {
    pub total_tracked: u64,
    pub compiled: u64,
    pub threshold: u64,
    pub hottest_uncompiled: Option<(String, u64)>,
}

#[derive(Debug, Clone, Copy)]
pub enum CallResult {
    /// Continue interpreting — not hot yet.
    Interpret,
    /// Function is JIT-compiled; use this pointer.
    Compiled(*const u8),
    /// Threshold crossed — compile this function now, then cache.
    CompileNow,
}

/// Global singleton for the JIT cache.
static GLOBAL_JIT_CACHE: OnceLock<Mutex<JitCache>> = OnceLock::new();

/// Get or initialize the global JIT cache.
pub fn global_jit_cache() -> &'static Mutex<JitCache> {
    GLOBAL_JIT_CACHE.get_or_init(|| {
        let threshold = std::env::var("SIMPLE_JIT_THRESHOLD")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(DEFAULT_JIT_THRESHOLD);

        let enabled = std::env::var("SIMPLE_JIT_CACHE")
            .map(|v| v != "0" && v.to_lowercase() != "false")
            .unwrap_or(true);

        Mutex::new(JitCache::new(if enabled { threshold } else { u64::MAX }))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn call_count_triggers_compile() {
        let mut cache = JitCache::new(3);

        assert!(matches!(cache.record_call("hot_fn"), CallResult::Interpret));
        assert!(matches!(cache.record_call("hot_fn"), CallResult::Interpret));
        assert!(matches!(cache.record_call("hot_fn"), CallResult::CompileNow));

        cache.store_compiled("hot_fn", 0xDEAD as *const u8);
        assert!(matches!(cache.record_call("hot_fn"), CallResult::Compiled(_)));
    }

    #[test]
    fn disabled_cache_always_interprets() {
        let mut cache = JitCache::new(1);
        cache.set_enabled(false);
        assert!(matches!(cache.record_call("any_fn"), CallResult::Interpret));
    }

    #[test]
    fn stats_report() {
        let mut cache = JitCache::new(5);
        for _ in 0..10 {
            cache.record_call("loop_fn");
        }
        cache.record_call("cold_fn");

        let stats = cache.stats();
        assert_eq!(stats.total_tracked, 2);
        assert_eq!(stats.compiled, 0);
        assert_eq!(stats.hottest_uncompiled.as_ref().unwrap().0, "loop_fn");
    }
}
