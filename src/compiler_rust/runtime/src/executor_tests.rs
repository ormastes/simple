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
    let handle = rt_thread_spawn_isolated(closure.as_ptr() as u64, RuntimeValue::from_int(21));

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
    let handle = rt_thread_spawn_isolated_with_args(
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
    let handle = rt_thread_spawn_isolated(closure.as_ptr() as u64, array);

    assert_eq!(handle, 0);
    crate::value::rt_array_free(array);
}

#[test]
fn test_isolated_thread_with_args_rejects_heap_graph_in_second_input() {
    let closure = native_closure_record(add_values as *const ());
    let array = crate::value::rt_array_new(1);
    let handle =
        rt_thread_spawn_isolated_with_args(closure.as_ptr() as u64, RuntimeValue::from_int(1), array);

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
    let handle = rt_thread_spawn_isolated(closure.as_ptr() as u64, channel);

    assert_ne!(handle, 0);
    assert_eq!(rt_thread_join(handle), RuntimeValue::TRUE);
    rt_thread_free(handle);
    crate::value::rt_channel_free(channel);
}

#[test]
fn test_limited_thread_rejects_mutable_heap_graph_before_spawn() {
    let closure = native_closure_record(double_value as *const ());
    let array = crate::value::rt_array_new(1);
    let handle = rt_thread_spawn_limited(closure.as_ptr() as u64, array, -1, -1, -1, -1);

    assert_eq!(handle, 0);
    crate::value::rt_array_free(array);
}

#[test]
fn test_limited_thread_with_args_rejects_heap_graph_in_second_input() {
    let closure = native_closure_record(add_values as *const ());
    let array = crate::value::rt_array_new(1);
    let handle = rt_thread_spawn_limited_with_args(
        closure.as_ptr() as u64,
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
    let handle = rt_thread_spawn_isolated(
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
    let handle = rt_thread_spawn_isolated(record_addr, RuntimeValue::from_int(40));
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
    let handle = rt_thread_spawn_isolated_with_args(
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
// The worker-argument ABI is a property of the closure WORD encoding only:
// an int-tagged word (addr << 3, above the user-VA ceiling) means the worker
// takes raw i64 parameters; a real record address means RuntimeValue
// parameters. It must never depend on where the allocator put the record,
// on test order, or on concurrent spawns.

#[test]
fn test_isolated_thread_heap_record_word_is_never_raw_abi() {
    // Many live records spread the allocator over its arenas; every real
    // record address must classify as the tagged (RuntimeValue) ABI.
    let records: Vec<_> = (0..4096).map(|_| native_closure_record(add_values as *const ())).collect();
    for r in &records {
        assert!(!native_word_exceeds_user_va(r.as_ptr() as u64));
    }
}

#[test]
fn test_isolated_thread_worker_args_stress_concurrent_spawners() {
    // Stress: 16 spawner threads x 32 spawns, closure and direct records,
    // interleaved. A shape/address heuristic or shared classification state
    // shows up here as a wrong sum (historically 5 or 36 instead of 42).
    extern "C" fn direct_add(left: RuntimeValue, right: RuntimeValue) -> RuntimeValue {
        RuntimeValue::from_int(left.as_int() + right.as_int())
    }
    let spawners: Vec<_> = (0..16)
        .map(|s| {
            thread::spawn(move || {
                for i in 0..32i64 {
                    let left = s * 1000 + i;
                    let record = if (s + i) % 2 == 0 {
                        native_closure_record(add_values as *const ())
                    } else {
                        native_direct_function_record(direct_add as *const ())
                    };
                    let handle = rt_thread_spawn_isolated_with_args(
                        record.as_ptr() as u64,
                        RuntimeValue::from_int(left),
                        RuntimeValue::from_int(42 - left),
                    );
                    assert!(handle != 0);
                    let result = rt_thread_join(handle);
                    assert!(result.is_int());
                    assert_eq!(result.as_int(), 42, "spawner {} iter {}", s, i);
                    rt_thread_free(handle);
                }
            })
        })
        .collect();
    for s in spawners {
        s.join().expect("spawner panicked");
    }
}

// Residual Windows-heap wrong-guess (owner decision 2026-11-06, P0): a record
// at a Windows heap address (~2^40) passed in the int-tagged form `addr << 3`
// stays below the user-VA ceiling. The VA-ceiling rule alone then reads the
// tagged word as the record address itself (access violation / wrong ABI).
// The classifier must validate both decodings against committed memory and
// pick the only valid one, failing closed when neither or both are valid.
#[cfg(windows)]
extern "C" fn add_raw_words(_closure: u64, a: u64, b: u64) -> RuntimeValue {
    RuntimeValue::from_int(a as i64 + b as i64)
}

#[cfg(windows)]
#[test]
fn test_isolated_thread_tagged_word_below_va_ceiling_selects_raw_abi() {
    let closure = native_closure_record(add_raw_words as *const ());
    let word = (closure.as_ptr() as u64) << 3;
    assert!(!native_word_exceeds_user_va(word), "fixture must sit below the ceiling");
    let handle = rt_thread_spawn_isolated_with_args(word, RuntimeValue::from_int(10), RuntimeValue::from_int(32));
    assert!(handle != 0);
    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);
    rt_thread_free(handle);
}

#[cfg(windows)]
#[test]
fn test_isolated_thread_classifier_decodes_both_word_forms() {
    let closure = native_closure_record(add_values as *const ());
    let addr = closure.as_ptr() as u64;
    match unsafe { native_callable(addr) } {
        Some(NativeCallable::ClosureRecord { closure_ptr, raw_worker_args, .. }) => {
            assert_eq!(closure_ptr, addr);
            assert!(!raw_worker_args);
        }
        _ => panic!("raw record address must classify as a RuntimeValue-ABI closure record"),
    }
    match unsafe { native_callable(addr << 3) } {
        Some(NativeCallable::ClosureRecord { closure_ptr, raw_worker_args, .. }) => {
            assert_eq!(closure_ptr, addr);
            assert!(raw_worker_args);
        }
        _ => panic!("tagged record word must classify as a raw-ABI closure record"),
    }
    let direct = native_direct_function_record(add_values as *const ());
    match unsafe { native_callable((direct.as_ptr() as u64) << 3) } {
        Some(NativeCallable::DirectFunction { raw_worker_args, .. }) => assert!(raw_worker_args),
        _ => panic!("tagged direct-function record must stay a direct function"),
    }
}

#[cfg(windows)]
#[test]
fn test_isolated_thread_unmapped_word_fails_closed() {
    // A word naming neither a committed record nor its tagged form must be
    // rejected (spawn returns 0), never dereferenced.
    let unmapped: u64 = 0x0000_1230_0000_0000;
    assert!(unsafe { native_callable(unmapped) }.is_none());
    assert_eq!(rt_thread_spawn_isolated(unmapped, RuntimeValue::from_int(1)), 0);
}

#[cfg(windows)]
#[test]
fn test_isolated_thread_tagged_and_raw_words_stress_concurrent_spawners() {
    // Stress: 16 spawners x 32 spawns interleaving raw record addresses
    // (RuntimeValue ABI) and below-ceiling tagged words (raw ABI). Any
    // shared/racy classification or address guess shows up as a wrong sum.
    let spawners: Vec<_> = (0..16)
        .map(|s| {
            thread::spawn(move || {
                for i in 0..32i64 {
                    let left = s * 1000 + i;
                    let tagged = (s + i) % 2 == 0;
                    let record = if tagged {
                        native_closure_record(add_raw_words as *const ())
                    } else {
                        native_closure_record(add_values as *const ())
                    };
                    let addr = record.as_ptr() as u64;
                    let word = if tagged { addr << 3 } else { addr };
                    let handle = rt_thread_spawn_isolated_with_args(
                        word,
                        RuntimeValue::from_int(left),
                        RuntimeValue::from_int(42 - left),
                    );
                    assert!(handle != 0, "spawner {} iter {}", s, i);
                    let result = rt_thread_join(handle);
                    assert!(result.is_int());
                    assert_eq!(result.as_int(), 42, "spawner {} iter {} tagged {}", s, i, tagged);
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
    let handle = rt_thread_spawn_isolated(closure.as_ptr() as u64, RuntimeValue::from_int(1));

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
