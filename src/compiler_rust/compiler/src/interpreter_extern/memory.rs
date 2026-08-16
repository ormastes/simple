//! Memory management extern functions
//!
//! Functions for querying and configuring memory limits for runner threads.

use super::mem_guard;
use crate::error::CompileError;
use crate::value::Value;
use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

// ============================================================================
// Hosted allocation metadata (rt_alloc / rt_free truth)
// ============================================================================

/// Size metadata for hosted `rt_alloc` allocations, keyed by pointer address.
/// Lets hosted `rt_free` reconstruct the layout and actually free, and keeps a
/// live-byte counter maintainable. Double-free stays refused: a pointer absent
/// from this map is never passed to the allocator.
static HOSTED_ALLOC_SIZES: OnceLock<Mutex<HashMap<usize, usize>>> = OnceLock::new();

/// Live bytes currently held by hosted `rt_alloc` allocations.
static HOSTED_LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);

fn hosted_alloc_sizes() -> &'static Mutex<HashMap<usize, usize>> {
    HOSTED_ALLOC_SIZES.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Record a successful hosted allocation.
fn hosted_alloc_record(ptr: usize, size: usize) {
    let mut map = hosted_alloc_sizes().lock().unwrap_or_else(|e| e.into_inner());
    map.insert(ptr, size);
    HOSTED_LIVE_BYTES.fetch_add(size, Ordering::Relaxed);
}

/// Take (remove) the recorded size for a hosted allocation.
/// Returns `None` for unknown pointers (double free / foreign pointer) —
/// callers must refuse to free in that case.
fn hosted_free_take(ptr: usize) -> Option<usize> {
    let mut map = hosted_alloc_sizes().lock().unwrap_or_else(|e| e.into_inner());
    let size = map.remove(&ptr)?;
    HOSTED_LIVE_BYTES.fetch_sub(size, Ordering::Relaxed);
    Some(size)
}

/// Current hosted rt_alloc live bytes (counter-based, exact).
pub fn hosted_live_alloc_bytes() -> usize {
    HOSTED_LIVE_BYTES.load(Ordering::Relaxed)
}

// ============================================================================
// HARDEN mode (SIMPLE_MEM_HARDEN=1): quarantine + poison-on-free
// ============================================================================
//
// Zig-GPA-style debug allocator for the hosted rt_alloc/rt_free path (plan
// M2 §3). Off by default — `harden_enabled()` is a cached `OnceLock<bool>`
// read, mirroring `simple_runtime::value::heap`'s `ATTR_ENABLED` pattern, so
// the off path costs one bool check before the existing free.
//
// On free: poison the block (0xDE bytes, distinct from GC white/gray/black
// flag bits) and defer the real `dealloc` through a bounded FIFO ring
// (capacity by BOTH slot count and byte budget) instead of freeing
// immediately, so a read-after-free from a stale pointer reads poison
// instead of silently working — and `rt_mem_harden_check()` can detect a
// *write*-after-free by finding a quarantined block whose bytes no longer
// match the poison pattern.

const HARDEN_POISON_BYTE: u8 = 0xDE;
/// Ring capacity by slot count (plan: "e.g. 256 slots").
const QUARANTINE_MAX_SLOTS: usize = 256;
/// Ring capacity by bytes (plan: "1MB cap") — bounds one huge free from
/// starving the ring, independent of the slot-count cap.
const QUARANTINE_MAX_BYTES: usize = 1024 * 1024;

static HARDEN_ENABLED: OnceLock<bool> = OnceLock::new();

/// Cached `SIMPLE_MEM_HARDEN=1` gate — read once, never per-alloc.
fn harden_enabled() -> bool {
    *HARDEN_ENABLED.get_or_init(|| std::env::var("SIMPLE_MEM_HARDEN").map(|v| v == "1").unwrap_or(false))
}

/// Programmatic enable, for tests only (the M3 `--mem-infra=harden` CLI path
/// is a separate milestone). Mirrors
/// `simple_runtime::value::heap::mem_attr_enable`'s `OnceLock::set` shape —
/// must run before the first `rt_free` call to win the race, later calls are
/// no-ops.
#[cfg(test)]
fn mem_harden_enable() {
    let _ = HARDEN_ENABLED.set(true);
}

struct QuarantineEntry {
    ptr: usize,
    size: usize,
}

#[derive(Default)]
struct QuarantineState {
    ring: VecDeque<QuarantineEntry>,
    bytes: usize,
}

static QUARANTINE: OnceLock<Mutex<QuarantineState>> = OnceLock::new();

fn quarantine() -> &'static Mutex<QuarantineState> {
    QUARANTINE.get_or_init(|| Mutex::new(QuarantineState::default()))
}

/// True if `ptr` currently sits in the quarantine ring (freed, not yet
/// really deallocated) — used to give double-free-of-a-quarantined-block the
/// same refusal as any other double free.
fn quarantine_contains(ptr: usize) -> bool {
    quarantine()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .ring
        .iter()
        .any(|e| e.ptr == ptr)
}

/// Poison `size` bytes at `ptr` and push onto the quarantine ring, evicting
/// (and genuinely deallocating, `Layout::from_size_align(size, 8)` — the
/// same alignment `rt_alloc` always uses) the oldest entries once either cap
/// is exceeded. `ptr`/`size` must be a just-removed `hosted_alloc_sizes`
/// entry (i.e. `rt_alloc` produced it and it has not already been freed).
fn harden_quarantine_free(ptr: usize, size: usize) {
    unsafe {
        std::ptr::write_bytes(ptr as *mut u8, HARDEN_POISON_BYTE, size);
    }
    let mut q = quarantine().lock().unwrap_or_else(|e| e.into_inner());
    q.ring.push_back(QuarantineEntry { ptr, size });
    q.bytes += size;
    while q.ring.len() > QUARANTINE_MAX_SLOTS || q.bytes > QUARANTINE_MAX_BYTES {
        let Some(evicted) = q.ring.pop_front() else { break };
        q.bytes -= evicted.size;
        if let Ok(layout) = std::alloc::Layout::from_size_align(evicted.size, 8) {
            unsafe {
                std::alloc::dealloc(evicted.ptr as *mut u8, layout);
            }
        }
    }
}

/// Write-after-free detector: scan every quarantined block for bytes that no
/// longer match the poison pattern. Returns the count of tampered blocks (0
/// = clean). Always 0 when harden is off.
///
/// Callable from Simple as: `rt_mem_harden_check() -> i64`
pub fn rt_mem_harden_check(_args: &[Value]) -> Result<Value, CompileError> {
    if !harden_enabled() {
        return Ok(Value::Int(0));
    }
    let q = quarantine().lock().unwrap_or_else(|e| e.into_inner());
    let mut tampered = 0i64;
    for entry in q.ring.iter() {
        let bytes = unsafe { std::slice::from_raw_parts(entry.ptr as *const u8, entry.size) };
        if bytes.iter().any(|&b| b != HARDEN_POISON_BYTE) {
            tampered += 1;
        }
    }
    Ok(Value::Int(tampered))
}

// ============================================================================
// GUARD mode (SIMPLE_MEM_GUARD_RATE=N): sampled guard-paged slots
// ============================================================================
//
// Thin extern surface over `mem_guard` — the mmap/mprotect mechanics live
// there (plan M2 §1-2); this module only owns the rt_alloc/rt_free hook
// points and the stats extern.

/// Sampled-allocation count so far (extern `rt_mem_guard_stats`). 0 whenever
/// `SIMPLE_MEM_GUARD_RATE` is unset — the zero-overhead-off default.
///
/// Callable from Simple as: `rt_mem_guard_stats() -> i64`
pub fn rt_mem_guard_stats(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(mem_guard::guard_sampled_count()))
}

// ============================================================================
// Memory-profiling capability surface
// ============================================================================

/// ABI version of the hosted memory-profiling surface.
pub const MEM_PROFILE_ABI_VERSION: i64 = 1;
/// bit0: exact heap-registry HEADER byte counters (rt_heap_live_bytes etc.).
pub const MEM_PROFILE_FEATURE_HEADER_BYTES: i64 = 1 << 0;
/// bit1: hosted rt_alloc size metadata (rt_free really frees, live bytes tracked).
pub const MEM_PROFILE_FEATURE_HOSTED_ALLOC_METADATA: i64 = 1 << 1;
/// bit2: memory_usage() reports real process RSS (not a stub).
pub const MEM_PROFILE_FEATURE_REAL_MEMORY_USAGE: i64 = 1 << 2;
/// bit3: per-owner allocation attribution (SIMPLE_MEM_ATTR=1, plan M1).
pub const MEM_PROFILE_FEATURE_OWNER_ATTRIBUTION: i64 = 1 << 3;

/// Memory-profiling ABI version.
///
/// Callable from Simple as: `rt_mem_profile_abi_version() -> i64`
pub fn rt_mem_profile_abi_version(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(MEM_PROFILE_ABI_VERSION))
}

/// Memory-profiling feature bitmask.
///
/// Callable from Simple as: `rt_mem_profile_features() -> i64`
/// bit0 = header-bytes, bit1 = hosted-alloc-metadata, bit2 = real-memory-usage.
pub fn rt_mem_profile_features(_args: &[Value]) -> Result<Value, CompileError> {
    let mut features = MEM_PROFILE_FEATURE_HEADER_BYTES | MEM_PROFILE_FEATURE_HOSTED_ALLOC_METADATA;
    if process_rss_bytes().is_some() {
        features |= MEM_PROFILE_FEATURE_REAL_MEMORY_USAGE;
    }
    if simple_runtime::value::heap::rt_mem_attr_enabled() != 0 {
        features |= MEM_PROFILE_FEATURE_OWNER_ATTRIBUTION;
    }
    Ok(Value::Int(features))
}

/// Whether per-owner allocation attribution is on (SIMPLE_MEM_ATTR=1).
///
/// Callable from Simple as: `rt_mem_attr_enabled() -> i64`
pub fn rt_mem_attr_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_runtime::value::heap::rt_mem_attr_enabled()))
}

/// Set the attribution owner label for subsequent allocations on this thread.
/// No-op when attribution is off.
///
/// Callable from Simple as: `rt_mem_attr_set_owner(name: text)`
pub fn rt_mem_attr_set_owner(args: &[Value]) -> Result<Value, CompileError> {
    if let Some(Value::Str(name)) = args.first() {
        simple_runtime::value::heap::set_current_owner(name.as_ref());
    }
    Ok(Value::Nil)
}

/// Top-n per-owner report as "name\tlive\tpeak\tallocs" rows.
///
/// Callable from Simple as: `rt_mem_attr_report(n: i64) -> text`
pub fn rt_mem_attr_report(args: &[Value]) -> Result<Value, CompileError> {
    let n = match args.first() {
        Some(Value::Int(n)) => (*n).max(0) as usize,
        _ => 16,
    };
    Ok(Value::Str(simple_runtime::value::heap::owner_report(n).into()))
}

/// Print the top-n per-owner report directly to stdout.
///
/// Mirrors the native runtime symbol of the same name (heap.rs) so the seed's
/// tree-walk interpreter has parity with natively compiled code.
///
/// Callable from Simple as: `rt_mem_attr_report_print(n: i64)`
pub fn rt_mem_attr_report_print(args: &[Value]) -> Result<Value, CompileError> {
    let n = match args.first() {
        Some(Value::Int(n)) => (*n).max(0) as usize,
        _ => 16,
    };
    println!("{}", simple_runtime::value::heap::owner_report(n));
    Ok(Value::Nil)
}

/// Get current memory usage in bytes
///
/// Callable from Simple as: `memory_usage()`
///
/// # Returns
/// * Real process RSS on Linux (/proc/self/statm); elsewhere a counter-based
///   value (heap-registry header bytes + hosted rt_alloc live bytes). Never a
///   hardcoded 0.
pub fn memory_usage(_args: &[Value]) -> Result<Value, CompileError> {
    let usage = get_current_memory_usage();
    Ok(Value::Int(usage as i64))
}

/// Return the hosted runtime's live heap-registry entry count.
pub fn rt_heap_registry_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_runtime::value::heap::rt_heap_registry_count()))
}

/// Return live heap-object header bytes.
///
/// Callable from Simple as: `rt_heap_live_bytes() -> i64`
pub fn rt_heap_live_bytes(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_runtime::value::heap::rt_heap_live_bytes()))
}

/// Return live container backing-buffer bytes.
///
/// Callable from Simple as: `rt_heap_aux_live_bytes() -> i64`
pub fn rt_heap_aux_live_bytes(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_runtime::value::heap::rt_heap_aux_live_bytes()))
}

/// Return live array element-buffer capacity bytes.
///
/// Callable from Simple as: `rt_heap_array_capacity_bytes() -> i64`
pub fn rt_heap_array_capacity_bytes(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_runtime::value::heap::rt_heap_array_capacity_bytes()))
}

/// Live header bytes for one `HeapObjectType` tag (0 for out-of-range kinds).
///
/// Callable from Simple as: `rt_heap_live_bytes_by_kind(kind: i64) -> i64`
pub fn rt_heap_live_bytes_by_kind(args: &[Value]) -> Result<Value, CompileError> {
    let kind = match args.first() {
        Some(Value::Int(k)) => *k,
        _ => return Ok(Value::Int(0)),
    };
    Ok(Value::Int(simple_runtime::value::heap::rt_heap_live_bytes_by_kind(kind)))
}

/// Live object count for one `HeapObjectType` tag (0 for out-of-range kinds).
///
/// Callable from Simple as: `rt_heap_live_count_by_kind(kind: i64) -> i64`
pub fn rt_heap_live_count_by_kind(args: &[Value]) -> Result<Value, CompileError> {
    let kind = match args.first() {
        Some(Value::Int(k)) => *k,
        _ => return Ok(Value::Int(0)),
    };
    Ok(Value::Int(simple_runtime::value::heap::rt_heap_live_count_by_kind(kind)))
}

/// Dispatch a hosted-runtime transient parser-array scope operation.
pub fn rt_transient_array_scope_begin(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(simple_runtime::value::rt_transient_array_scope_begin()))
}

pub fn rt_transient_array_scope_pause(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(simple_runtime::value::rt_transient_array_scope_pause()))
}

pub fn rt_transient_heap_promote(args: &[Value]) -> Result<Value, CompileError> {
    let Some(value) = args.first() else {
        return Ok(Value::Bool(false));
    };
    let promoted = match value {
        // Raw runtime handles cross the interpreter boundary as integer carriers.
        Value::Int(raw) => {
            simple_runtime::value::rt_transient_heap_promote(simple_runtime::value::RuntimeValue::from_raw(*raw as u64))
        }
        Value::UInt { value, .. } => {
            simple_runtime::value::rt_transient_heap_promote(simple_runtime::value::RuntimeValue::from_raw(*value))
        }
        Value::Nil => false,
        // Interpreter composites are Arc/owned Rust values, not allocations in
        // the runtime transient scope, so they are already retained.
        _ => true,
    };
    Ok(Value::Bool(promoted))
}

pub fn rt_transient_array_scope_end(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(simple_runtime::value::rt_transient_array_scope_end()))
}

/// Get memory limit in bytes (0 if unlimited)
///
/// Callable from Simple as: `memory_limit()`
///
/// # Returns
/// * Memory limit in bytes as an integer (0 = unlimited)
pub fn memory_limit(_args: &[Value]) -> Result<Value, CompileError> {
    let limit = get_current_memory_limit();
    Ok(Value::Int(limit as i64))
}

/// Get memory usage as percentage of limit (0-100)
///
/// Callable from Simple as: `memory_usage_percent()`
///
/// # Returns
/// * Memory usage as percentage (0.0 if unlimited)
pub fn memory_usage_percent(_args: &[Value]) -> Result<Value, CompileError> {
    let limit = get_current_memory_limit();
    if limit == 0 {
        return Ok(Value::Float(0.0));
    }
    let usage = get_current_memory_usage();
    let percent = (usage as f64 / limit as f64) * 100.0;
    Ok(Value::Float(percent))
}

/// Check if memory is limited
///
/// Callable from Simple as: `is_memory_limited()`
///
/// # Returns
/// * Bool indicating whether memory limit is enabled
pub fn is_memory_limited(_args: &[Value]) -> Result<Value, CompileError> {
    let limit = get_current_memory_limit();
    Ok(Value::Bool(limit > 0))
}

/// Get default memory limit constant (1 GB)
///
/// Callable from Simple as: `default_memory_limit()`
///
/// # Returns
/// * Default memory limit in bytes (1 GB)
pub fn default_memory_limit(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_common::gc::DEFAULT_MEMORY_LIMIT as i64))
}

/// Format bytes as human-readable string
///
/// Callable from Simple as: `format_bytes(bytes)`
///
/// # Arguments
/// * `args` - [bytes: Int]
///
/// # Returns
/// * Formatted string (e.g., "1.5 GB", "256 MB", "1024 KB")
pub fn format_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let bytes = args
        .first()
        .ok_or_else(|| CompileError::runtime("format_bytes requires 1 argument (bytes)"))?
        .as_int()? as usize;

    let formatted = if bytes >= 1024 * 1024 * 1024 {
        format!("{:.2} GB", bytes as f64 / (1024.0 * 1024.0 * 1024.0))
    } else if bytes >= 1024 * 1024 {
        format!("{:.2} MB", bytes as f64 / (1024.0 * 1024.0))
    } else if bytes >= 1024 {
        format!("{:.2} KB", bytes as f64 / 1024.0)
    } else {
        format!("{} bytes", bytes)
    };

    Ok(Value::text(formatted))
}

/// Parse a memory size string (e.g., "100M", "2G")
///
/// Callable from Simple as: `parse_memory_size(size_str)`
///
/// # Arguments
/// * `args` - [size_str: String]
///
/// # Returns
/// * Size in bytes as Int, or -1 if invalid
pub fn parse_memory_size(args: &[Value]) -> Result<Value, CompileError> {
    let size_str = args
        .first()
        .ok_or_else(|| CompileError::runtime("parse_memory_size requires 1 argument (size_str)"))?;

    let s = match size_str {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("parse_memory_size: argument must be a string")),
    };

    let result = parse_size_string(&s).unwrap_or(usize::MAX);
    if result == usize::MAX {
        Ok(Value::Int(-1))
    } else {
        Ok(Value::Int(result as i64))
    }
}

/// Convert raw IEEE-754 bits to f32.
pub fn f32_from_bits(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("f32_from_bits requires 1 argument (bits)"));
    }

    let bits = args[0].as_int()? as u32;
    Ok(Value::Float(f32::from_bits(bits) as f64))
}

pub fn spl_i64_is_zero(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("spl_i64_is_zero requires 1 argument (value)"));
    }
    let value = args[0].as_int()?;
    Ok(Value::Int(if value == 0 { 1 } else { 0 }))
}

// Internal helper functions

/// Real process resident-set size on Linux, from /proc/self/statm
/// (field 1 = resident pages) * page size. `None` off-Linux or on parse failure.
#[cfg(target_os = "linux")]
fn process_rss_bytes() -> Option<usize> {
    let statm = std::fs::read_to_string("/proc/self/statm").ok()?;
    let rss_pages: usize = statm.split_whitespace().nth(1)?.parse().ok()?;
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if page_size <= 0 {
        return None;
    }
    Some(rss_pages * page_size as usize)
}

#[cfg(not(target_os = "linux"))]
fn process_rss_bytes() -> Option<usize> {
    None
}

fn get_current_memory_usage() -> usize {
    // Prefer OS truth (real RSS). Fall back to exact counters we do maintain:
    // heap-registry header bytes + hosted rt_alloc live bytes.
    process_rss_bytes().unwrap_or_else(|| {
        let heap_header_bytes = simple_runtime::value::heap::rt_heap_live_bytes().max(0) as usize;
        heap_header_bytes + hosted_live_alloc_bytes()
    })
}

fn get_current_memory_limit() -> usize {
    // Return the default memory limit
    // In a full implementation, this would query the thread-local allocator
    simple_common::gc::DEFAULT_MEMORY_LIMIT
}

fn parse_size_string(s: &str) -> Option<usize> {
    let s = s.trim().to_uppercase();

    if let Some(num) = s.strip_suffix("GB") {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix('G') {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix("MB") {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix('M') {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix("KB") {
        num.trim().parse::<usize>().ok().map(|n| n * 1024)
    } else if let Some(num) = s.strip_suffix('K') {
        num.trim().parse::<usize>().ok().map(|n| n * 1024)
    } else {
        s.parse::<usize>().ok()
    }
}

// ============================================================================
// System Allocator Functions
// ============================================================================

/// Allocate memory with specified size and alignment
///
/// Callable from Simple as: `sys_malloc(size, align)`
///
/// # Arguments
/// * `args` - [size: usize, align: usize]
///
/// # Returns
/// * Byte array representing allocated memory pointer
pub fn sys_malloc(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime("sys_malloc requires 2 arguments (size, align)"));
    }

    let size = args[0].as_int()? as usize;
    let align = args[1].as_int()? as usize;

    // Allocate memory using Rust's allocator
    let layout = std::alloc::Layout::from_size_align(size, align)
        .map_err(|_| CompileError::runtime("sys_malloc: invalid size or alignment"))?;

    unsafe {
        let ptr = std::alloc::alloc(layout);
        if ptr.is_null() {
            return Err(CompileError::runtime("sys_malloc: allocation failed"));
        }

        // Return pointer as a single-element byte array containing the pointer address
        // We use a trick: encode the pointer as an Int value
        Ok(Value::Int(ptr as i64))
    }
}

/// Free memory allocated by sys_malloc
///
/// Callable from Simple as: `sys_free(ptr, size, align)`
///
/// # Arguments
/// * `args` - [ptr: [u8], size: usize, align: usize]
pub fn sys_free(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "sys_free requires 3 arguments (ptr, size, align)",
        ));
    }

    let ptr_val = args[0].as_int()?;
    let size = args[1].as_int()? as usize;
    let align = args[2].as_int()? as usize;

    if ptr_val == 0 {
        // Null pointer - nothing to free
        return Ok(Value::Nil);
    }

    // Deallocate memory
    let layout = std::alloc::Layout::from_size_align(size, align)
        .map_err(|_| CompileError::runtime("sys_free: invalid size or alignment"))?;

    unsafe {
        let ptr = ptr_val as *mut u8;
        std::alloc::dealloc(ptr, layout);
    }

    Ok(Value::Nil)
}

// ============================================================================
// Raw Memory Operations (for LLVM-lib SFFI backend)
// ============================================================================

/// Allocate zeroed memory with alignment 8.
///
/// Callable from Simple as: `rt_alloc(size: i64) -> i64`
/// Returns pointer as i64, 0 on failure.
pub fn rt_alloc(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_alloc requires 1 argument (size)"));
    }
    let size = args[0].as_int()? as usize;
    if size == 0 {
        return Ok(Value::Int(0));
    }
    // GUARD mode: 1-in-N sampled allocations land on their own guard-paged
    // mmap slot instead of the normal allocator. Falls through to the
    // normal path on mmap/mprotect failure rather than failing the alloc.
    if mem_guard::mem_guard_should_sample(size) {
        let owner = simple_runtime::value::heap::current_owner_id();
        if let Some(ptr) = mem_guard::guard_alloc_sampled(size, owner) {
            return Ok(Value::Int(ptr as i64));
        }
    }
    let layout =
        std::alloc::Layout::from_size_align(size, 8).map_err(|_| CompileError::runtime("rt_alloc: invalid size"))?;
    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout);
        if ptr.is_null() {
            return Ok(Value::Int(0));
        }
        hosted_alloc_record(ptr as usize, size);
        Ok(Value::Int(ptr as usize as i64))
    }
}

/// Free memory allocated by rt_alloc. No-op for null pointers.
///
/// Callable from Simple as: `rt_free(ptr: i64)`
///
/// The allocation size is looked up from the hosted metadata map, so the
/// memory is genuinely deallocated. Unknown pointers (double free or a
/// pointer rt_alloc never produced) are refused: nothing is freed.
pub fn rt_free(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_free requires 1 argument (ptr)"));
    }
    let ptr_val = args[0].as_int()?;
    if ptr_val == 0 {
        return Ok(Value::Nil);
    }
    let ptr = ptr_val as usize;
    // GUARD mode: sampled pointers never went through hosted_alloc_sizes —
    // mprotect(PROT_NONE) the slot (UAF trap) instead of deallocating.
    // A double free here is refused by guard_free_sampled itself.
    if mem_guard::guard_is_slot(ptr) {
        mem_guard::guard_free_sampled(ptr);
        return Ok(Value::Nil);
    }
    let Some(size) = hosted_free_take(ptr) else {
        // Double free (including of an already-quarantined block) or a
        // foreign pointer — refuse (do not touch the allocator).
        return Ok(Value::Nil);
    };
    // HARDEN mode: poison + defer the real free through the quarantine ring
    // instead of deallocating now.
    if harden_enabled() {
        harden_quarantine_free(ptr, size);
        return Ok(Value::Nil);
    }
    // Layout mirrors rt_alloc (align 8); size came from the metadata map.
    let layout = std::alloc::Layout::from_size_align(size, 8)
        .map_err(|_| CompileError::runtime("rt_free: corrupt allocation metadata"))?;
    unsafe {
        std::alloc::dealloc(ptr as *mut u8, layout);
    }
    Ok(Value::Nil)
}

/// Write i64 value at addr+offset.
///
/// Callable from Simple as: `rt_ptr_write_i64(addr: i64, offset: i64, value: i64)`
pub fn rt_ptr_write_i64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_ptr_write_i64 requires 3 arguments (addr, offset, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let offset = args[1].as_int()?;
    let value = args[2].as_int()?;
    unsafe {
        let ptr = (addr as *mut u8).offset(offset as isize) as *mut i64;
        ptr.write(value);
    }
    Ok(Value::Nil)
}

/// Read i64 value from addr+offset.
///
/// Callable from Simple as: `rt_ptr_read_i64(addr: i64, offset: i64) -> i64`
pub fn rt_ptr_read_i64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_ptr_read_i64 requires 2 arguments (addr, offset)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let offset = args[1].as_int()?;
    unsafe {
        let ptr = (addr as *const u8).offset(offset as isize) as *const i64;
        Ok(Value::Int(ptr.read()))
    }
}

/// Read one unsigned byte from addr+offset without over-reading.
pub fn rt_ptr_read_u8(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_ptr_read_u8 requires 2 arguments (addr, offset)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let offset = args[1].as_int()?;
    unsafe {
        let ptr = (addr as *const u8).offset(offset as isize);
        Ok(Value::Int(ptr.read() as i64))
    }
}

/// Hosted interpreter bridge for the loader's raw mmap contract.
#[cfg(unix)]
pub fn rt_mmap_raw(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 6 {
        return Err(CompileError::runtime("rt_mmap_raw requires 6 arguments"));
    }
    let addr = args[0].as_int()? as usize as *mut libc::c_void;
    let length = args[1].as_int()?;
    if length <= 0 {
        return Ok(Value::Int(-1));
    }
    let mapped = unsafe {
        libc::mmap(
            addr,
            length as usize,
            args[2].as_int()? as i32,
            args[3].as_int()? as i32,
            args[4].as_int()? as i32,
            args[5].as_int()? as libc::off_t,
        )
    };
    if mapped == libc::MAP_FAILED {
        Ok(Value::Int(-1))
    } else {
        Ok(Value::Int(mapped as usize as i64))
    }
}

#[cfg(not(unix))]
pub fn rt_mmap_raw(_args: &[Value]) -> Result<Value, CompileError> {
    Err(CompileError::runtime("rt_mmap_raw is unavailable on this host"))
}

#[cfg(unix)]
pub fn rt_munmap_raw(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("rt_munmap_raw requires 2 arguments"));
    }
    let result = unsafe {
        libc::munmap(
            args[0].as_int()? as usize as *mut libc::c_void,
            args[1].as_int()? as usize,
        )
    };
    Ok(Value::Int(i64::from(result)))
}

#[cfg(not(unix))]
pub fn rt_munmap_raw(_args: &[Value]) -> Result<Value, CompileError> {
    Err(CompileError::runtime("rt_munmap_raw is unavailable on this host"))
}

#[cfg(unix)]
pub fn rt_mprotect(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime("rt_mprotect requires 3 arguments"));
    }
    let result = unsafe {
        libc::mprotect(
            args[0].as_int()? as usize as *mut libc::c_void,
            args[1].as_int()? as usize,
            args[2].as_int()? as i32,
        )
    };
    Ok(Value::Int(i64::from(result)))
}

#[cfg(not(unix))]
pub fn rt_mprotect(_args: &[Value]) -> Result<Value, CompileError> {
    Err(CompileError::runtime("rt_mprotect is unavailable on this host"))
}

#[cfg(test)]
mod ptr_read_u8_tests {
    use super::{rt_mmap_raw, rt_mprotect, rt_munmap_raw, rt_ptr_read_u8};
    use crate::value::Value;

    #[cfg(unix)]
    #[test]
    fn reads_exact_unsigned_byte_offsets() {
        let bytes = [0x00_u8, 0x7f, 0x80, 0xff, 0x5a];
        let addr = bytes.as_ptr() as usize as i64;
        for (offset, expected) in bytes.iter().enumerate() {
            let value = rt_ptr_read_u8(&[
                Value::Int(addr),
                Value::Int(offset as i64),
            ])
            .expect("byte read");
            assert_eq!(value.as_int().expect("integer byte"), i64::from(*expected));
        }
    }

    #[test]
    fn rejects_missing_arguments() {
        assert!(rt_ptr_read_u8(&[]).is_err());
        assert!(rt_ptr_read_u8(&[Value::Int(1)]).is_err());
    }

    #[test]
    fn maps_protects_and_unmaps_host_memory() {
        let mapped = rt_mmap_raw(&[
            Value::Int(0),
            Value::Int(4096),
            Value::Int(libc::PROT_READ as i64 | libc::PROT_WRITE as i64),
            Value::Int(libc::MAP_PRIVATE as i64 | libc::MAP_ANONYMOUS as i64),
            Value::Int(-1),
            Value::Int(0),
        ])
        .unwrap()
        .as_int()
        .unwrap();
        assert_ne!(mapped, -1);
        assert_eq!(
            rt_mprotect(&[
                Value::Int(mapped),
                Value::Int(4096),
                Value::Int(libc::PROT_READ as i64),
            ])
            .unwrap()
            .as_int()
            .unwrap(),
            0
        );
        assert_eq!(
            rt_munmap_raw(&[Value::Int(mapped), Value::Int(4096)])
                .unwrap()
                .as_int()
                .unwrap(),
            0
        );
    }
}

/// Read i32 value from addr+offset.
///
/// Callable from Simple as: `rt_ptr_read_i32(addr: i64, offset: i64) -> i32`
pub fn rt_ptr_read_i32(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_ptr_read_i32 requires 2 arguments (addr, offset)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let offset = args[1].as_int()?;
    unsafe {
        let ptr = (addr as *const u8).offset(offset as isize) as *const i32;
        Ok(Value::Int(ptr.read() as i64))
    }
}

/// Write i32 value at addr+offset.
///
/// Callable from Simple as: `rt_ptr_write_i32(addr: i64, offset: i64, value: i64)`
pub fn rt_ptr_write_i32(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_ptr_write_i32 requires 3 arguments (addr, offset, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let offset = args[1].as_int()?;
    let value = args[2].as_int()? as i32;
    unsafe {
        let ptr = (addr as *mut u8).offset(offset as isize) as *mut i32;
        ptr.write(value);
    }
    Ok(Value::Nil)
}

/// Volatile MMIO/RAM read/write primitives (u8/u16/u32), single address arg
/// (no offset) — mirrors `rt_mmio_*` in
/// `src/runtime/startup/baremetal/runtime_minimal.c`, which is compiled only
/// into baremetal SimpleOS images and is absent from every hosted build.
/// Hosted callers (e.g. `src/os/gui/render.spl`'s shadow-buffer path, which
/// always targets a plain `rt_alloc`ed RAM address in this tree, never a real
/// device register) need the identical volatile-pointer semantics, so this is
/// a genuine implementation, not a mock/double: the same read-what-was-written
/// contract holds on both RAM and true MMIO. See
/// doc/08_tracking/bug/render_spl_specs_cannot_execute_mmio_externs_2026-08-06.md.
///
/// Callable from Simple as: `rt_mmio_read_u32(addr: u64) -> u32`
pub fn rt_mmio_read_u32(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_mmio_read_u32 requires 1 argument (addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u32).read_volatile() as i64)) }
}

/// Callable from Simple as: `rt_mmio_write_u32(addr: u64, value: u32)`
pub fn rt_mmio_write_u32(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_mmio_write_u32 requires 2 arguments (addr, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u32;
    unsafe { (addr as *mut u32).write_volatile(value) };
    Ok(Value::Nil)
}

/// Callable from Simple as: `rt_mmio_read_u16(addr: u64) -> u16`
pub fn rt_mmio_read_u16(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_mmio_read_u16 requires 1 argument (addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u16).read_volatile() as i64)) }
}

/// Callable from Simple as: `rt_mmio_write_u16(addr: u64, value: u16)`
pub fn rt_mmio_write_u16(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_mmio_write_u16 requires 2 arguments (addr, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u16;
    unsafe { (addr as *mut u16).write_volatile(value) };
    Ok(Value::Nil)
}

/// Callable from Simple as: `rt_mmio_read_u8(addr: u64) -> u8`
pub fn rt_mmio_read_u8(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_mmio_read_u8 requires 1 argument (addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u8).read_volatile() as i64)) }
}

/// Callable from Simple as: `rt_mmio_write_u8(addr: u64, value: u8)`
pub fn rt_mmio_write_u8(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_mmio_write_u8 requires 2 arguments (addr, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u8;
    unsafe { (addr as *mut u8).write_volatile(value) };
    Ok(Value::Nil)
}


/// Volatile read/write family mirroring the native runtime's
/// `rt_volatile_read_u{8,16,32,64}` / `rt_volatile_write_u{8,16,32,64}`
/// (src/compiler_rust/runtime/src/lib.rs:379-417, all `(addr: i64 [, value:
/// i64])` C-ABI). Under the tree-walk interpreter these serve spec harnesses
/// whose "mmio" region is a plain `rt_alloc`ed process-memory buffer (mock
/// ivshmem), so a plain load/store through the pointer is faithful — no real
/// volatile ordering semantics are needed here; `read_volatile`/
/// `write_volatile` are used anyway to match the JIT lane byte-for-byte.
/// Addresses are treated strictly as process-memory addresses, same as the
/// sibling `rt_ptr_*`/`rt_mmio_*` accessors above. See
/// doc/08_tracking/bug/interpreter_missing_rt_volatile_externs_blocks_ivshmem_specs_2026-08-15.md.
///
/// Callable from Simple as: `rt_volatile_read_u8(addr: i64) -> i64`
pub fn rt_volatile_read_u8(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_volatile_read_u8 requires 1 argument (addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u8).read_volatile() as i64)) }
}

/// Callable from Simple as: `rt_volatile_read_u16(addr: i64) -> i64`
pub fn rt_volatile_read_u16(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_volatile_read_u16 requires 1 argument (addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u16).read_volatile() as i64)) }
}

/// Callable from Simple as: `rt_volatile_read_u32(addr: i64) -> i64`
pub fn rt_volatile_read_u32(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_volatile_read_u32 requires 1 argument (addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u32).read_volatile() as i64)) }
}

/// Callable from Simple as: `rt_volatile_read_u64(addr: i64) -> i64`
pub fn rt_volatile_read_u64(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_volatile_read_u64 requires 1 argument (addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u64).read_volatile() as i64)) }
}

/// Callable from Simple as: `rt_volatile_write_u8(addr: i64, value: i64)`
pub fn rt_volatile_write_u8(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_volatile_write_u8 requires 2 arguments (addr, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u8;
    unsafe { (addr as *mut u8).write_volatile(value) };
    Ok(Value::Nil)
}

/// Callable from Simple as: `rt_volatile_write_u16(addr: i64, value: i64)`
pub fn rt_volatile_write_u16(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_volatile_write_u16 requires 2 arguments (addr, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u16;
    unsafe { (addr as *mut u16).write_volatile(value) };
    Ok(Value::Nil)
}

/// Callable from Simple as: `rt_volatile_write_u32(addr: i64, value: i64)`
pub fn rt_volatile_write_u32(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_volatile_write_u32 requires 2 arguments (addr, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u32;
    unsafe { (addr as *mut u32).write_volatile(value) };
    Ok(Value::Nil)
}

/// Callable from Simple as: `rt_volatile_write_u64(addr: i64, value: i64)`
pub fn rt_volatile_write_u64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_volatile_write_u64 requires 2 arguments (addr, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u64;
    unsafe { (addr as *mut u64).write_volatile(value) };
    Ok(Value::Nil)
}

/// Read one byte from a raw address (hosted/interpreter counterpart of a
/// kernel `copy_from_user`).
///
/// This is the same trust model as the other `rt_ptr_*`/`rt_mmio_*` raw
/// accessors in this file: it performs an unvalidated volatile read of the
/// given address. It does NOT walk page tables or check VMA permissions —
/// callers on the OS kernel side (`_copy_user_bytes`/`_copy_user_u64`/
/// `_copy_user_cstr` in `src/os/kernel/ipc/syscall_process.spl`) are
/// responsible for validating the address range (via `_is_user_read_range`/
/// `_is_userspace_range`) *before* calling this, exactly as the sibling
/// `_vmm_read_physmap_byte` path validates via `vmm_pt_range_user_readable`
/// before touching physical memory. Under the hosted interpreter (specs),
/// "user" addresses are genuine addresses in the interpreter's own process
/// (e.g. `rt_string_data(...)`), so a raw read is correct here, matching
/// `rt_ptr_read_i64`/`rt_mmio_read_u8`.
///
/// Callable from Simple as: `rt_copy_user_byte(ptr_addr: u64) -> u8`
pub fn rt_copy_user_byte(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_copy_user_byte requires 1 argument (ptr_addr)"));
    }
    let addr = args[0].as_int()? as usize;
    unsafe { Ok(Value::Int((addr as *const u8).read_volatile() as i64)) }
}

/// Write u8 value at addr+offset.
///
/// Callable from Simple as: `rt_ptr_write_u8(addr: i64, offset: i64, value: i64)`
pub fn rt_ptr_write_u8(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_ptr_write_u8 requires 3 arguments (addr, offset, value)",
        ));
    }
    let addr = args[0].as_int()? as usize;
    let offset = args[1].as_int()?;
    let value = args[2].as_int()? as u8;
    unsafe {
        let ptr = (addr as *mut u8).offset(offset as isize);
        ptr.write(value);
    }
    Ok(Value::Nil)
}

/// Fill memory with a byte value.
///
/// Callable from Simple as: `rt_memset(addr: i64, value: i64, n: i64) -> i64`
/// Returns the destination address.
pub fn rt_memset(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime("rt_memset requires 3 arguments (addr, value, n)"));
    }
    let addr = args[0].as_int()? as usize;
    let value = args[1].as_int()? as u8;
    let n = args[2].as_int()? as usize;
    unsafe {
        std::ptr::write_bytes(addr as *mut u8, value, n);
    }
    Ok(Value::Int(addr as i64))
}

/// Copy memory from src to dst.
///
/// Callable from Simple as: `rt_memcpy(dst: i64, src: i64, n: i64) -> i64`
/// Returns the destination address.
pub fn rt_memcpy(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime("rt_memcpy requires 3 arguments (dst, src, n)"));
    }
    let dst = args[0].as_int()? as usize;
    let src = args[1].as_int()? as usize;
    let n = args[2].as_int()? as usize;
    unsafe {
        std::ptr::copy_nonoverlapping(src as *const u8, dst as *mut u8, n);
    }
    Ok(Value::Int(dst as i64))
}

/// Reallocate memory
///
/// Callable from Simple as: `sys_realloc(ptr, old_size, new_size, align)`
///
/// # Arguments
/// * `args` - [ptr: [u8], old_size: usize, new_size: usize, align: usize]
///
/// # Returns
/// * New pointer as byte array
pub fn sys_realloc(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime(
            "sys_realloc requires 4 arguments (ptr, old_size, new_size, align)",
        ));
    }

    let ptr_val = args[0].as_int()?;
    let old_size = args[1].as_int()? as usize;
    let new_size = args[2].as_int()? as usize;
    let align = args[3].as_int()? as usize;

    let old_layout = std::alloc::Layout::from_size_align(old_size, align)
        .map_err(|_| CompileError::runtime("sys_realloc: invalid old size or alignment"))?;

    unsafe {
        let old_ptr = ptr_val as *mut u8;
        let new_ptr = std::alloc::realloc(old_ptr, old_layout, new_size);

        if new_ptr.is_null() {
            return Err(CompileError::runtime("sys_realloc: reallocation failed"));
        }

        Ok(Value::Int(new_ptr as i64))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alloc(size: i64) -> i64 {
        rt_alloc(&[Value::Int(size)]).unwrap().as_int().unwrap()
    }

    fn map_contains(ptr: i64) -> bool {
        hosted_alloc_sizes()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .contains_key(&(ptr as usize))
    }

    #[test]
    fn rt_alloc_records_size_metadata() {
        let ptr = alloc(64);
        assert_ne!(ptr, 0, "rt_alloc(64) must not fail");
        assert!(map_contains(ptr), "allocation must be recorded in the metadata map");
        let recorded = hosted_alloc_sizes()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(&(ptr as usize))
            .copied();
        assert_eq!(recorded, Some(64));
        assert!(hosted_live_alloc_bytes() >= 64);
        rt_free(&[Value::Int(ptr)]).unwrap();
    }

    #[test]
    fn rt_free_releases_and_double_free_is_refused() {
        let ptr = alloc(128);
        assert_ne!(ptr, 0);
        let live_before_free = hosted_live_alloc_bytes();

        rt_free(&[Value::Int(ptr)]).unwrap();
        assert!(!map_contains(ptr), "freed pointer must leave the metadata map");
        // Counter drops by exactly this allocation's size relative to the
        // pre-free snapshot (other tests only add, never remove, our entry).
        assert!(hosted_live_alloc_bytes() <= live_before_free - 128);

        // Double free: pointer no longer in the map -> must be refused, not crash.
        let result = rt_free(&[Value::Int(ptr)]);
        assert!(result.is_ok(), "double free must be refused gracefully");
        assert!(!map_contains(ptr));
    }

    #[test]
    fn rt_free_refuses_foreign_pointer() {
        // A pointer rt_alloc never produced must not reach the allocator.
        let bogus = 0xDEAD_B000_i64;
        assert!(!map_contains(bogus));
        assert!(rt_free(&[Value::Int(bogus)]).is_ok());
    }

    #[test]
    fn rt_free_null_is_noop() {
        assert!(rt_free(&[Value::Int(0)]).is_ok());
    }

    #[test]
    fn memory_usage_is_positive() {
        // Hold a live hosted allocation so even the counter fallback is > 0.
        let ptr = alloc(4096);
        let usage = memory_usage(&[]).unwrap().as_int().unwrap();
        assert!(usage > 0, "memory_usage() must not report 0, got {usage}");
        rt_free(&[Value::Int(ptr)]).unwrap();
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn memory_usage_reports_real_rss_on_linux() {
        let rss = process_rss_bytes().expect("statm RSS must parse on Linux");
        // Any live Rust test process is at least 1 MiB resident.
        assert!(rss > 1024 * 1024, "implausible RSS: {rss}");
        let usage = memory_usage(&[]).unwrap().as_int().unwrap() as usize;
        assert!(usage > 1024 * 1024);
    }

    #[test]
    fn mem_profile_capability_externs() {
        let version = rt_mem_profile_abi_version(&[]).unwrap().as_int().unwrap();
        assert_eq!(version, 1);
        let features = rt_mem_profile_features(&[]).unwrap().as_int().unwrap();
        assert_ne!(features & MEM_PROFILE_FEATURE_HEADER_BYTES, 0);
        assert_ne!(features & MEM_PROFILE_FEATURE_HOSTED_ALLOC_METADATA, 0);
        #[cfg(target_os = "linux")]
        assert_ne!(features & MEM_PROFILE_FEATURE_REAL_MEMORY_USAGE, 0);
    }

    #[test]
    fn transient_heap_promote_accepts_interpreter_owned_graphs() {
        let graph = Value::Array(std::sync::Arc::new(vec![Value::Int(1)]));
        assert!(matches!(rt_transient_heap_promote(&[graph]), Ok(Value::Bool(true))));
        assert!(matches!(
            rt_transient_heap_promote(&[Value::Int(0)]),
            Ok(Value::Bool(false))
        ));
        assert!(matches!(
            rt_transient_heap_promote(&[Value::UInt { value: 0, width: 64 }]),
            Ok(Value::Bool(false))
        ));
        assert!(matches!(rt_transient_heap_promote(&[]), Ok(Value::Bool(false))));
    }

    // ========================================================================
    // HARDEN mode (SIMPLE_MEM_HARDEN=1): quarantine + poison-on-free (M2 §3)
    // ========================================================================

    #[test]
    fn harden_quarantine_catches_write_after_free() {
        mem_harden_enable();
        let ptr = alloc(64);
        assert_ne!(ptr, 0);
        assert!(!quarantine_contains(ptr as usize), "not quarantined before free");

        rt_free(&[Value::Int(ptr)]).unwrap();
        // Freed pointer must be gone from the live map (same observable
        // contract as the non-harden path) but the block itself is NOT
        // really deallocated yet — it sits in the quarantine ring.
        assert!(!map_contains(ptr), "freed pointer must leave the live metadata map");
        assert!(quarantine_contains(ptr as usize), "freed block must enter the quarantine ring");

        // Read-after-free: the block is poisoned (0xDE), not garbage/reused.
        let byte = unsafe { std::ptr::read(ptr as *const u8) };
        assert_eq!(byte, HARDEN_POISON_BYTE, "quarantined block must read as poison before tampering");
        assert_eq!(rt_mem_harden_check(&[]).unwrap().as_int().unwrap(), 0, "untouched quarantine must report clean");

        // Write-after-free: tamper one byte through the stale pointer.
        unsafe {
            std::ptr::write(ptr as *mut u8, 0x41);
        }
        let tampered = rt_mem_harden_check(&[]).unwrap().as_int().unwrap();
        assert!(tampered >= 1, "rt_mem_harden_check must report >=1 tampered block, got {tampered}");

        // Double free of a quarantined (not really-freed) block must still
        // be refused, not touch the allocator.
        assert!(rt_free(&[Value::Int(ptr)]).is_ok());
    }

    #[test]
    fn harden_quarantine_reuse_impossible_before_eviction() {
        mem_harden_enable();
        let ptr = alloc(32);
        rt_free(&[Value::Int(ptr)]).unwrap();
        // A fresh allocation of the same size must not reuse the still-quarantined
        // block's address — the real `dealloc` for it has not happened yet, so
        // the system allocator cannot have handed the address back out.
        let ptr2 = alloc(32);
        assert_ne!(ptr, 0);
        assert_ne!(ptr2, 0);
        assert_ne!(ptr, ptr2, "quarantined block's address must not be reused before ring eviction");
        rt_free(&[Value::Int(ptr2)]).unwrap();
    }

    // ========================================================================
    // GUARD mode (SIMPLE_MEM_GUARD_RATE=N): sampled guard-paged slots (M2 §1-2)
    // ========================================================================

    #[test]
    fn rt_mem_guard_stats_extern_returns_a_count() {
        // Off by default (no env set in this process): count is a
        // non-negative counter, and calling the extern never panics/errors.
        // (mem_guard's own unit tests cover the sampled-alloc bookkeeping in
        // detail; this just exercises the extern wiring end to end.)
        let count = rt_mem_guard_stats(&[]).unwrap().as_int().unwrap();
        assert!(count >= 0);
    }
}
