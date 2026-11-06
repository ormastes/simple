use super::*;
use std::sync::atomic::{AtomicI32, AtomicI64};
use std::time::Duration;

#[test]
fn test_threaded_mode() {
    let executor = FutureExecutor::new(AsyncMode::Threaded);
    executor.set_worker_count(2);
    executor.start();

    let counter = Arc::new(AtomicI32::new(0));
    let counter_clone = counter.clone();

    executor.submit(move || {
        counter_clone.fetch_add(1, Ordering::SeqCst);
    });

    // Wait a bit for the task to complete
    thread::sleep(Duration::from_millis(100));

    assert_eq!(counter.load(Ordering::SeqCst), 1);
    executor.shutdown();
}

#[test]
fn test_threaded_mode_current_task_id() {
    let executor = FutureExecutor::new(AsyncMode::Threaded);
    executor.set_worker_count(1);
    executor.start();

    let observed = Arc::new(AtomicI64::new(0));
    let observed_clone = observed.clone();

    let task_id = executor.submit(move || {
        observed_clone.store(rt_executor_current_task_id(), Ordering::SeqCst);
    });

    let deadline = std::time::Instant::now() + Duration::from_millis(500);
    while observed.load(Ordering::SeqCst) == 0 && std::time::Instant::now() < deadline {
        thread::sleep(Duration::from_millis(5));
    }

    assert_eq!(observed.load(Ordering::SeqCst), task_id as i64);
    assert_eq!(rt_executor_current_task_id(), 0);
    executor.shutdown();
}

#[test]
fn test_manual_mode() {
    let executor = FutureExecutor::new(AsyncMode::Manual);

    let counter = Arc::new(AtomicI32::new(0));
    let counter_clone = counter.clone();

    executor.submit(move || {
        counter_clone.fetch_add(1, Ordering::SeqCst);
    });

    // Task should not execute until polled
    assert_eq!(counter.load(Ordering::SeqCst), 0);
    assert_eq!(executor.pending_count(), 1);

    // Now poll
    assert!(executor.poll_one());
    assert_eq!(counter.load(Ordering::SeqCst), 1);
    assert_eq!(executor.pending_count(), 0);
}

#[test]
fn test_manual_mode_current_task_id() {
    let executor = FutureExecutor::new(AsyncMode::Manual);

    let observed = Arc::new(AtomicI64::new(0));
    let observed_clone = observed.clone();

    let task_id = executor.submit(move || {
        observed_clone.store(rt_executor_current_task_id(), Ordering::SeqCst);
    });

    assert_eq!(rt_executor_current_task_id(), 0);
    assert!(executor.poll_one());
    assert_eq!(observed.load(Ordering::SeqCst), task_id as i64);
    assert_eq!(rt_executor_current_task_id(), 0);
}

#[test]
fn test_promise() {
    let promise: Promise<i32> = Promise::new();
    let promise_clone = promise.clone();

    assert_eq!(promise.state(), PromiseState::Pending);

    thread::spawn(move || {
        thread::sleep(Duration::from_millis(10));
        promise_clone.resolve(42);
    });

    let result = promise.wait();
    assert_eq!(result, Ok(42));
    assert_eq!(promise.state(), PromiseState::Fulfilled);
}

#[test]
fn test_promise_reject() {
    let promise: Promise<i32> = Promise::new();
    promise.reject("error".to_string());

    assert_eq!(promise.state(), PromiseState::Rejected);
    assert_eq!(promise.try_get(), Some(Err("error".to_string())));
}

// ========================================================================
// Panic-boundary tests (W2-1)
// ========================================================================

#[test]
fn test_worker_survives_panicking_task() {
    // A task that panics must not kill the worker; a subsequent task must complete.
    let executor = FutureExecutor::new(AsyncMode::Threaded);
    executor.set_worker_count(1);
    executor.start();

    // Submit a panicking task with a unique sentinel string.
    executor.submit(|| {
        panic!("W2-1-sentinel-panic-7f3a2b");
    });

    // Give the worker time to process the panic.
    thread::sleep(Duration::from_millis(100));

    // The panic message must have been recorded.
    let recorded = take_last_task_panic();
    assert!(
        recorded.as_deref().unwrap_or("").contains("W2-1-sentinel-panic-7f3a2b"),
        "expected sentinel in last-panic slot, got: {:?}",
        recorded
    );

    // Worker must still be alive: submit a normal task and verify it runs.
    let counter = Arc::new(std::sync::atomic::AtomicI32::new(0));
    let counter_clone = counter.clone();
    executor.submit(move || {
        counter_clone.fetch_add(1, Ordering::SeqCst);
    });

    let deadline = std::time::Instant::now() + Duration::from_millis(500);
    while counter.load(Ordering::SeqCst) == 0 && std::time::Instant::now() < deadline {
        thread::sleep(Duration::from_millis(5));
    }
    assert_eq!(
        counter.load(Ordering::SeqCst),
        1,
        "worker did not survive panicking task"
    );

    executor.shutdown();
}

// ========================================================================
// Isolated Thread tests
// ========================================================================

fn native_closure_record(func: *const ()) -> Box<[usize; 2]> {
    // Word 1 is read for the direct-function marker; keep it in bounds.
    Box::new([func as usize, 0])
}

fn native_direct_function_record(func: *const ()) -> Box<[usize; 2]> {
    Box::new([func as usize, NATIVE_DIRECT_FUNCTION_RECORD_MARKER])
}

extern "C" fn double_value(_closure: u64, v: RuntimeValue) -> RuntimeValue {
    let n = v.as_int();
    RuntimeValue::from_int(n * 2)
}

extern "C" fn add_values(_closure: u64, v1: RuntimeValue, v2: RuntimeValue) -> RuntimeValue {
    let a = v1.as_int();
    let b = v2.as_int();
    RuntimeValue::from_int(a + b)
}

#[test]
fn test_isolated_thread_spawn_and_join() {
    let closure = native_closure_record(double_value as *const ());
    let handle = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, closure.as_ptr() as u64, RuntimeValue::from_int(21));

    assert!(handle != 0);
    assert!(rt_thread_id(handle) > 0);

    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);

    rt_thread_free(handle);
}

#[test]
fn test_isolated_thread_spawn_with_args_and_join() {
    let closure = native_closure_record(add_values as *const ());
    let handle = rt_thread_spawn_isolated_with_args_kind(RT_WORKER_CLOSURE_ADDRESS,
        closure.as_ptr() as u64,
        RuntimeValue::from_int(10),
        RuntimeValue::from_int(32),
    );

    assert!(handle != 0);

    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);

    rt_thread_free(handle);
}

#[test]
fn test_isolated_thread_rejects_mutable_heap_graph_before_spawn() {
    let closure = native_closure_record(double_value as *const ());
    let array = crate::value::rt_array_new(1);
    let handle = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, closure.as_ptr() as u64, array);

    assert_eq!(handle, 0);
    crate::value::rt_array_free(array);
}

#[test]
fn test_isolated_thread_with_args_rejects_heap_graph_in_second_input() {
    let closure = native_closure_record(add_values as *const ());
    let array = crate::value::rt_array_new(1);
    let handle =
        rt_thread_spawn_isolated_with_args_kind(RT_WORKER_CLOSURE_ADDRESS, closure.as_ptr() as u64, RuntimeValue::from_int(1), array);

    assert_eq!(handle, 0);
    crate::value::rt_array_free(array);
}

#[test]
fn test_isolated_thread_accepts_synchronized_channel_handle() {
    extern "C" fn channel_worker(_closure: u64, value: RuntimeValue) -> RuntimeValue {
        RuntimeValue::from_bool(value.heap_type() == Some(crate::value::HeapObjectType::Channel))
    }

    let closure = native_closure_record(channel_worker as *const ());
    let channel = crate::value::rt_channel_new();
    let handle = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, closure.as_ptr() as u64, channel);

    assert_ne!(handle, 0);
    assert_eq!(rt_thread_join(handle), RuntimeValue::TRUE);
    rt_thread_free(handle);
    crate::value::rt_channel_free(channel);
}

#[test]
fn test_limited_thread_rejects_mutable_heap_graph_before_spawn() {
    let closure = native_closure_record(double_value as *const ());
    let array = crate::value::rt_array_new(1);
    let handle = rt_thread_spawn_limited(closure.as_ptr() as u64 | 1, array, -1, -1, -1, -1);

    assert_eq!(handle, 0);
    crate::value::rt_array_free(array);
}

#[test]
fn test_limited_thread_with_args_rejects_heap_graph_in_second_input() {
    let closure = native_closure_record(add_values as *const ());
    let array = crate::value::rt_array_new(1);
    let handle = rt_thread_spawn_limited_with_args(
        closure.as_ptr() as u64 | 1,
        RuntimeValue::from_int(1),
        array,
        -1,
        -1,
        -1,
        -1,
    );

    assert_eq!(handle, 0);
    crate::value::rt_array_free(array);
}

#[test]
fn test_isolated_thread_spawn_and_join_direct_function_record() {
    // A direct-function entry takes no hidden environment argument.
    extern "C" fn direct_worker(v: RuntimeValue) -> RuntimeValue {
        RuntimeValue::from_int(v.as_int() + 1)
    }

    let closure = native_direct_function_record(direct_worker as *const ());
    let handle = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, 
        (&*closure) as *const [usize; 2] as *const usize as u64,
        RuntimeValue::from_int(41),
    );

    assert!(handle != 0);
    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);

    rt_thread_free(handle);
}

#[test]
fn test_isolated_thread_static_direct_record_is_data_not_code() {
    // A record in a loaded object's data segment resolves under dladdr, so
    // dladdr alone would call the record itself as code. It also sits above
    // 2^47 on aarch64 PIE, which the old x86_64-only ceiling read as an
    // int-tagged word.
    extern "C" fn static_direct_worker(v: RuntimeValue) -> RuntimeValue {
        RuntimeValue::from_int(v.as_int() + 2)
    }
    #[repr(C)]
    struct DirectRecord {
        entry: extern "C" fn(RuntimeValue) -> RuntimeValue,
        marker: usize,
    }
    static RECORD: DirectRecord = DirectRecord {
        entry: static_direct_worker,
        marker: NATIVE_DIRECT_FUNCTION_RECORD_MARKER,
    };
    let record_addr = &RECORD as *const DirectRecord as u64;
    assert!(!native_word_exceeds_user_va(record_addr));
    let handle = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, record_addr, RuntimeValue::from_int(40));
    assert!(handle != 0);
    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);
    rt_thread_free(handle);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_native_word_user_va_ceiling_aarch64() {
    // 48-bit user VA; a Top-Byte-Ignore tag is not part of the address.
    assert!(!native_word_exceeds_user_va(0x0000_ffff_ffff_fff8));
    assert!(!native_word_exceeds_user_va(0x5a00_aaaa_aaab_0000));
    // addr << 3 of an aarch64 PIE address lands above the ceiling.
    assert!(native_word_exceeds_user_va(0x0000_aaaa_aaab_0000u64 << 3));
}

#[test]
fn test_isolated_thread_spawn_with_args_and_join_direct_function_record() {
    extern "C" fn direct_add(left: RuntimeValue, right: RuntimeValue) -> RuntimeValue {
        RuntimeValue::from_int(left.as_int() + right.as_int())
    }

    let closure = native_direct_function_record(direct_add as *const ());
    let handle = rt_thread_spawn_isolated_with_args_kind(RT_WORKER_CLOSURE_ADDRESS,
        (&*closure) as *const [usize; 2] as *const usize as u64,
        RuntimeValue::from_int(10),
        RuntimeValue::from_int(32),
    );

    assert!(handle != 0);
    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);

    rt_thread_free(handle);
}

// doc/08_tracking/bug/isolated_thread_raw_worker_argument_heuristic_flake_2026-08-12.md
// The worker ABI is an explicit kind chosen by the spawner, never inferred
// from the closure word's value. ADDRESS: machine address, RuntimeValue args.
// VALUE: tagged RuntimeValue decoded by its own tag -- TAG_INT (addr << 3) is
// a raw native record with raw i64 args, TAG_HEAP (addr | 1) a heap record
// with RuntimeValue args. Results must not depend on where the allocator put
// a record, on test order, or on concurrent spawns.

extern "C" fn add_raw_words(_closure: u64, a: u64, b: u64) -> RuntimeValue {
    RuntimeValue::from_int(a as i64 + b as i64)
}

extern "C" fn direct_add_raw(a: u64, b: u64) -> RuntimeValue {
    RuntimeValue::from_int(a as i64 + b as i64)
}

extern "C" fn direct_add_values(left: RuntimeValue, right: RuntimeValue) -> RuntimeValue {
    RuntimeValue::from_int(left.as_int() + right.as_int())
}

#[test]
fn test_worker_closure_kind_decode_is_explicit() {
    let addr: u64 = 0x0000_0001_0000_0000;
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_ADDRESS, addr), Some((addr, false)));
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_VALUE, addr << 3), Some((addr, true)));
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_VALUE, addr | 1), Some((addr, false)));
    // The same word means different things under different kinds -- the kind,
    // not the value, decides.
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_ADDRESS, addr << 3), Some((addr << 3, false)));
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_VALUE, addr), Some((addr >> 3, true)));
    // Rejections: unknown kinds, non-callable RuntimeValue tags (nil, bool,
    // float...), payloads in the null page, and "addresses" above user VA.
    for kind in [0, 3, -1, i64::MAX] {
        assert_eq!(native_worker_closure_word(kind, addr), None, "kind {}", kind);
    }
    for tag in 2..8u64 {
        assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_VALUE, addr | tag), None, "tag {}", tag);
    }
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_VALUE, RuntimeValue::NIL.0), None);
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_VALUE, 4095 << 3), None);
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_ADDRESS, 4095), None);
    assert_eq!(native_worker_closure_word(RT_WORKER_CLOSURE_ADDRESS, u64::MAX & !0x7), None);
    assert_eq!(rt_thread_spawn_isolated_kind(0, addr, RuntimeValue::from_int(1)), 0);
}

#[test]
fn test_isolated_thread_value_int_tagged_record_selects_raw_abi_at_any_address() {
    // Every heap address, including ones far below the old VA-ceiling cutoff,
    // decodes the same way: the tag says raw ABI.
    for _ in 0..64 {
        let closure = native_closure_record(add_raw_words as *const ());
        let word = (closure.as_ptr() as u64) << 3;
        let handle = rt_thread_spawn_isolated_with_args(word, RuntimeValue::from_int(10), RuntimeValue::from_int(32));
        assert!(handle != 0);
        assert_eq!(rt_thread_join(handle).as_int(), 42);
        rt_thread_free(handle);
    }
}

#[test]
fn test_isolated_thread_value_heap_tagged_record_keeps_runtime_value_abi() {
    let closure = native_closure_record(add_values as *const ());
    let word = (closure.as_ptr() as u64) | 1;
    let handle = rt_thread_spawn_isolated_with_args(word, RuntimeValue::from_int(10), RuntimeValue::from_int(32));
    assert!(handle != 0);
    assert_eq!(rt_thread_join(handle).as_int(), 42);
    rt_thread_free(handle);
}

#[test]
fn test_isolated_thread_classifier_follows_kind_not_value() {
    let closure = native_closure_record(add_values as *const ());
    let addr = closure.as_ptr() as u64;
    match unsafe { native_callable(RT_WORKER_CLOSURE_ADDRESS, addr) } {
        Some(NativeCallable::ClosureRecord { closure_ptr, raw_worker_args, .. }) => {
            assert_eq!(closure_ptr, addr);
            assert!(!raw_worker_args);
        }
        _ => panic!("ADDRESS record must classify as a RuntimeValue-ABI closure record"),
    }
    match unsafe { native_callable(RT_WORKER_CLOSURE_VALUE, addr << 3) } {
        Some(NativeCallable::ClosureRecord { closure_ptr, raw_worker_args, .. }) => {
            assert_eq!(closure_ptr, addr);
            assert!(raw_worker_args);
        }
        _ => panic!("VALUE int-tagged record must classify as a raw-ABI closure record"),
    }
    let direct = native_direct_function_record(add_values as *const ());
    match unsafe { native_callable(RT_WORKER_CLOSURE_VALUE, (direct.as_ptr() as u64) << 3) } {
        Some(NativeCallable::DirectFunction { raw_worker_args, .. }) => assert!(raw_worker_args),
        _ => panic!("VALUE int-tagged direct-function record must stay a direct function"),
    }
}

#[cfg(windows)]
#[test]
fn test_isolated_thread_unmapped_word_fails_closed() {
    // A record word naming no committed memory is rejected, never read.
    let unmapped: u64 = 0x0000_1230_0000_0000;
    assert!(unsafe { native_callable(RT_WORKER_CLOSURE_ADDRESS, unmapped) }.is_none());
    assert_eq!(rt_thread_spawn_isolated(unmapped << 3, RuntimeValue::from_int(1)), 0);
    assert_eq!(
        rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, unmapped, RuntimeValue::from_int(1)),
        0
    );
}

// Two committed records at A and A << 3, each with a code entry: the word
// A << 3 is a valid machine address AND a valid int-tagged RuntimeValue. Any
// value-based classifier must guess (the 2026-11-06 resolver rejected it as
// ambiguous; the VA-ceiling rule took the address). With an explicit kind the
// spawner's declaration decides, so both spawns succeed deterministically and
// reach DIFFERENT workers.
struct DualDecodeFixture {
    low: usize,
    high: usize,
}

#[cfg(windows)]
unsafe fn map_fixed_page(addr: usize) -> bool {
    use windows_sys::Win32::System::Memory::{VirtualAlloc, MEM_COMMIT, MEM_RESERVE, PAGE_READWRITE};
    VirtualAlloc(addr as *const std::ffi::c_void, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE) as usize == addr
}

#[cfg(windows)]
unsafe fn unmap_page(addr: usize) {
    use windows_sys::Win32::System::Memory::{VirtualFree, MEM_RELEASE};
    VirtualFree(addr as *mut std::ffi::c_void, 0, MEM_RELEASE);
}

#[cfg(unix)]
unsafe fn map_fixed_page(addr: usize) -> bool {
    let p = libc::mmap(
        addr as *mut libc::c_void,
        4096,
        libc::PROT_READ | libc::PROT_WRITE,
        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
        -1,
        0,
    );
    if p == libc::MAP_FAILED {
        return false;
    }
    if p as usize != addr {
        libc::munmap(p, 4096);
        return false;
    }
    true
}

#[cfg(unix)]
unsafe fn unmap_page(addr: usize) {
    libc::munmap(addr as *mut libc::c_void, 4096);
}

impl DualDecodeFixture {
    fn new() -> Self {
        // Windows allocation granularity is 64 KiB, so both pages are 64 KiB
        // aligned. A << 3 stays below every user-VA ceiling, so the word is a
        // plausible address on every host.
        for shift in [28u32, 30, 32, 34, 36, 38, 40] {
            for slot in 1..8usize {
                let low = (slot << shift) + 0x10000 * 3;
                let high = low << 3;
                unsafe {
                    if !map_fixed_page(low) {
                        continue;
                    }
                    if !map_fixed_page(high) {
                        unmap_page(low);
                        continue;
                    }
                    *(low as *mut [usize; 2]) = [add_raw_words as *const () as usize, 0];
                    *(high as *mut [usize; 2]) = [add_values as *const () as usize, 0];
                }
                return DualDecodeFixture { low, high };
            }
        }
        panic!("could not map a dual-decode fixture page pair");
    }
}

impl Drop for DualDecodeFixture {
    fn drop(&mut self) {
        unsafe {
            unmap_page(self.low);
            unmap_page(self.high);
        }
    }
}

#[test]
fn test_isolated_thread_dual_decodable_word_follows_declared_kind() {
    let fx = DualDecodeFixture::new();
    let word = fx.high as u64;
    assert_eq!(word, (fx.low as u64) << 3);
    assert!(!native_word_exceeds_user_va(word));
    // VALUE: int-tagged -> record at A, raw worker (add_raw_words).
    let h = rt_thread_spawn_isolated_with_args(word, RuntimeValue::from_int(10), RuntimeValue::from_int(32));
    assert!(h != 0, "VALUE spawn of a dual-decodable word must not be rejected");
    assert_eq!(rt_thread_join(h).as_int(), 42);
    rt_thread_free(h);
    // ADDRESS: record at A << 3, RuntimeValue worker (add_values).
    let h = rt_thread_spawn_isolated_with_args_kind(
        RT_WORKER_CLOSURE_ADDRESS,
        word,
        RuntimeValue::from_int(10),
        RuntimeValue::from_int(32),
    );
    assert!(h != 0, "ADDRESS spawn of a dual-decodable word must not be rejected");
    assert_eq!(rt_thread_join(h).as_int(), 42);
    rt_thread_free(h);
}

#[test]
fn test_isolated_thread_explicit_kind_stress_concurrent_spawners() {
    // Stress: 16 spawners x 64 spawns = 1024 spawns per run, interleaving
    // every encoding (VALUE int-tagged raw, VALUE heap-tagged, ADDRESS,
    // direct-function records, and the dual-decodable fixture word) with
    // integer arguments that look like pointers (record addresses, page
    // multiples, values below 4096). A value-based classifier shows up as a
    // wrong sum or a rejected spawn.
    let fx = std::sync::Arc::new(DualDecodeFixture::new());
    let spawners: Vec<_> = (0..16i64)
        .map(|s| {
            let fx = fx.clone();
            thread::spawn(move || {
                for i in 0..64i64 {
                    let rv_record = native_closure_record(add_values as *const ());
                    let raw_record = native_closure_record(add_raw_words as *const ());
                    let rv_direct = native_direct_function_record(direct_add_values as *const ());
                    let raw_direct = native_direct_function_record(direct_add_raw as *const ());
                    let left = match i % 4 {
                        0 => raw_record.as_ptr() as i64,
                        1 => fx.low as i64,
                        2 => 0x1000 * (s + 1),
                        _ => 8 * i,
                    };
                    let right = 42 - left;
                    let (kind, word) = match (s + i) % 6 {
                        0 => (RT_WORKER_CLOSURE_VALUE, (raw_record.as_ptr() as u64) << 3),
                        1 => (RT_WORKER_CLOSURE_VALUE, (rv_record.as_ptr() as u64) | 1),
                        2 => (RT_WORKER_CLOSURE_ADDRESS, rv_record.as_ptr() as u64),
                        3 => (RT_WORKER_CLOSURE_VALUE, (raw_direct.as_ptr() as u64) << 3),
                        4 => (RT_WORKER_CLOSURE_ADDRESS, rv_direct.as_ptr() as u64),
                        _ if i % 2 == 0 => (RT_WORKER_CLOSURE_VALUE, fx.high as u64),
                        _ => (RT_WORKER_CLOSURE_ADDRESS, fx.high as u64),
                    };
                    let handle = rt_thread_spawn_isolated_with_args_kind(
                        kind,
                        word,
                        RuntimeValue::from_int(left),
                        RuntimeValue::from_int(right),
                    );
                    assert!(handle != 0, "spawner {} iter {} kind {} rejected", s, i, kind);
                    let result = rt_thread_join(handle);
                    assert!(result.is_int());
                    assert_eq!(result.as_int(), 42, "spawner {} iter {} kind {}", s, i, kind);
                    rt_thread_free(handle);
                }
            })
        })
        .collect();
    for s in spawners {
        s.join().expect("spawner panicked");
    }
}

#[test]
fn test_isolated_thread_legacy_value_entry_stress_concurrent_spawners() {
    // Same stress through the Simple-facing legacy entry (kind VALUE):
    // int-tagged raw records, heap-tagged records, and the dual-decodable
    // word, 16 x 64 = 1024 spawns per run.
    let fx = std::sync::Arc::new(DualDecodeFixture::new());
    let spawners: Vec<_> = (0..16i64)
        .map(|s| {
            let fx = fx.clone();
            thread::spawn(move || {
                for i in 0..64i64 {
                    let rv_record = native_closure_record(add_values as *const ());
                    let raw_record = native_closure_record(add_raw_words as *const ());
                    let left = if i % 2 == 0 { raw_record.as_ptr() as i64 } else { 0x1000 * (s + 1) };
                    let word = match (s + i) % 3 {
                        0 => (raw_record.as_ptr() as u64) << 3,
                        1 => (rv_record.as_ptr() as u64) | 1,
                        _ => fx.high as u64,
                    };
                    let handle = rt_thread_spawn_isolated_with_args(
                        word,
                        RuntimeValue::from_int(left),
                        RuntimeValue::from_int(42 - left),
                    );
                    assert!(handle != 0, "spawner {} iter {} word {:#x} rejected", s, i, word);
                    let result = rt_thread_join(handle);
                    assert_eq!(result.as_int(), 42, "spawner {} iter {} word {:#x}", s, i, word);
                    rt_thread_free(handle);
                }
            })
        })
        .collect();
    for s in spawners {
        s.join().expect("spawner panicked");
    }
}

#[test]
fn test_isolated_thread_is_done() {
    extern "C" fn slow_work(_closure: u64, v: RuntimeValue) -> RuntimeValue {
        thread::sleep(Duration::from_millis(50));
        v
    }

    let closure = native_closure_record(slow_work as *const ());
    let handle = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, closure.as_ptr() as u64, RuntimeValue::from_int(1));

    // Thread should not be done immediately
    assert_eq!(rt_thread_is_done(handle), 0);

    // Wait for completion
    let result = rt_thread_join(handle);
    assert!(result.is_int());

    // Now should be done
    assert_eq!(rt_thread_is_done(handle), 1);

    rt_thread_free(handle);
}

#[test]
fn test_thread_available_parallelism() {
    let cores = rt_thread_available_parallelism();
    assert!(cores >= 1);
}

#[test]
fn test_thread_sleep() {
    let start = std::time::Instant::now();
    rt_thread_sleep(50);
    let elapsed = start.elapsed();
    assert!(elapsed >= Duration::from_millis(40));
}

#[test]
fn test_thread_yield() {
    // Just verify it doesn't panic
    rt_thread_yield();
}
