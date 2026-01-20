use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use simple_runtime::value::ffi::concurrent::{
    rt_concurrent_map_new, rt_concurrent_map_free, rt_concurrent_map_insert, rt_concurrent_map_get,
    rt_concurrent_map_remove,
    rt_concurrent_queue_new, rt_concurrent_queue_free, rt_concurrent_queue_push, rt_concurrent_queue_pop,
    rt_concurrent_stack_new, rt_concurrent_stack_free, rt_concurrent_stack_push, rt_concurrent_stack_pop,
    rt_pool_new, rt_pool_free, rt_pool_acquire, rt_pool_release,
    rt_arena_new, rt_arena_free, rt_arena_alloc,
    rt_tls_new, rt_tls_free, rt_tls_set, rt_tls_get,
};
use simple_runtime::value::RuntimeValue;
use std::sync::Arc;
use std::thread;

/// Benchmark map operations with varying thread counts
fn bench_map_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("map_operations");

    for num_threads in [1, 4, 8, 16] {
        group.throughput(Throughput::Elements(100_000));

        // 80% read, 15% insert, 5% remove workload
        group.bench_with_input(
            BenchmarkId::new("mixed_workload", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let map_handle = rt_concurrent_map_new();
                    let map_handle = Arc::new(map_handle);

                    let handles: Vec<_> = (0..num_threads)
                        .map(|thread_id| {
                            let map_handle = Arc::clone(&map_handle);
                            thread::spawn(move || {
                                let ops_per_thread = 100_000 / num_threads as usize;
                                for i in 0..ops_per_thread {
                                    let key = ((thread_id * 10000 + i) % 1000) as i64;
                                    let value = RuntimeValue::from_int(i as i64);

                                    let op_type = i % 100;
                                    if op_type < 80 {
                                        // 80% reads
                                        black_box(rt_concurrent_map_get(*map_handle, key));
                                    } else if op_type < 95 {
                                        // 15% inserts
                                        black_box(rt_concurrent_map_insert(*map_handle, key, value));
                                    } else {
                                        // 5% removes
                                        black_box(rt_concurrent_map_remove(*map_handle, key));
                                    }
                                }
                            })
                        })
                        .collect();

                    for handle in handles {
                        handle.join().unwrap();
                    }

                    rt_concurrent_map_free(*map_handle);
                });
            },
        );

        // Pure insert workload (high contention)
        group.bench_with_input(
            BenchmarkId::new("insert_only", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let map_handle = rt_concurrent_map_new();
                    let map_handle = Arc::new(map_handle);

                    let handles: Vec<_> = (0..num_threads)
                        .map(|thread_id| {
                            let map_handle = Arc::clone(&map_handle);
                            thread::spawn(move || {
                                let ops_per_thread = 10_000 / num_threads as usize;
                                for i in 0..ops_per_thread {
                                    let key = (thread_id * 10000 + i) as i64;
                                    let value = RuntimeValue::from_int(i as i64);
                                    black_box(rt_concurrent_map_insert(*map_handle, key, value));
                                }
                            })
                        })
                        .collect();

                    for handle in handles {
                        handle.join().unwrap();
                    }

                    rt_concurrent_map_free(*map_handle);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark queue operations with varying thread counts
fn bench_queue_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("queue_operations");

    for num_threads in [1, 4, 8, 16] {
        group.throughput(Throughput::Elements(100_000));

        // Producer-consumer workload
        group.bench_with_input(
            BenchmarkId::new("producer_consumer", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let queue_handle = rt_concurrent_queue_new();
                    let queue_handle = Arc::new(queue_handle);

                    let producers = num_threads / 2;
                    let consumers = num_threads - producers;

                    let mut handles = vec![];

                    // Producer threads
                    for thread_id in 0..producers {
                        let queue_handle = Arc::clone(&queue_handle);
                        handles.push(thread::spawn(move || {
                            let ops_per_thread = 100_000 / producers as usize;
                            for i in 0..ops_per_thread {
                                let value = RuntimeValue::from_int((thread_id * 100000 + i) as i64);
                                black_box(rt_concurrent_queue_push(*queue_handle, value));
                            }
                        }));
                    }

                    // Consumer threads
                    for _ in 0..consumers {
                        let queue_handle = Arc::clone(&queue_handle);
                        handles.push(thread::spawn(move || {
                            let ops_per_thread = 100_000 / consumers as usize;
                            for _ in 0..ops_per_thread {
                                loop {
                                    let val = rt_concurrent_queue_pop(*queue_handle);
                                    if val != RuntimeValue::NIL {
                                        black_box(val);
                                        break;
                                    }
                                    thread::yield_now();
                                }
                            }
                        }));
                    }

                    for handle in handles {
                        handle.join().unwrap();
                    }

                    rt_concurrent_queue_free(*queue_handle);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark stack operations with varying thread counts
fn bench_stack_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("stack_operations");

    for num_threads in [1, 4, 8, 16] {
        group.throughput(Throughput::Elements(100_000));

        // Mixed push/pop workload
        group.bench_with_input(
            BenchmarkId::new("mixed_push_pop", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let stack_handle = rt_concurrent_stack_new();
                    let stack_handle = Arc::new(stack_handle);

                    // Pre-populate stack
                    for i in 0..10_000 {
                        rt_concurrent_stack_push(*stack_handle, RuntimeValue::from_int(i));
                    }

                    let handles: Vec<_> = (0..num_threads)
                        .map(|thread_id| {
                            let stack_handle = Arc::clone(&stack_handle);
                            thread::spawn(move || {
                                let ops_per_thread = 100_000 / num_threads as usize;
                                for i in 0..ops_per_thread {
                                    if i % 2 == 0 {
                                        let value = RuntimeValue::from_int((thread_id * 100000 + i) as i64);
                                        black_box(rt_concurrent_stack_push(*stack_handle, value));
                                    } else {
                                        black_box(rt_concurrent_stack_pop(*stack_handle));
                                    }
                                }
                            })
                        })
                        .collect();

                    for handle in handles {
                        handle.join().unwrap();
                    }

                    rt_concurrent_stack_free(*stack_handle);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark pool operations with varying thread counts
fn bench_pool_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("pool_operations");

    for num_threads in [1, 4, 8, 16] {
        group.throughput(Throughput::Elements(100_000));

        // Acquire/release workload
        group.bench_with_input(
            BenchmarkId::new("acquire_release", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let pool_handle = rt_pool_new(1000);
                    let pool_handle = Arc::new(pool_handle);

                    // Pre-populate pool
                    for i in 0..1000 {
                        rt_pool_release(*pool_handle, RuntimeValue::from_int(i));
                    }

                    let handles: Vec<_> = (0..num_threads)
                        .map(|_| {
                            let pool_handle = Arc::clone(&pool_handle);
                            thread::spawn(move || {
                                let ops_per_thread = 100_000 / num_threads as usize;
                                for _ in 0..ops_per_thread {
                                    let value = rt_pool_acquire(*pool_handle);
                                    if value != RuntimeValue::NIL {
                                        black_box(rt_pool_release(*pool_handle, value));
                                    }
                                }
                            })
                        })
                        .collect();

                    for handle in handles {
                        handle.join().unwrap();
                    }

                    rt_pool_free(*pool_handle);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark arena operations with varying thread counts
fn bench_arena_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("arena_operations");

    for num_threads in [1, 4, 8, 16] {
        group.throughput(Throughput::Elements(50_000));

        // Alloc/free workload
        group.bench_with_input(
            BenchmarkId::new("alloc_free", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let arena_handle = rt_arena_new(1024 * 1024); // 1MB arena
                    let arena_handle = Arc::new(arena_handle);

                    let handles: Vec<_> = (0..num_threads)
                        .map(|_| {
                            let arena_handle = Arc::clone(&arena_handle);
                            thread::spawn(move || {
                                let ops_per_thread = 50_000 / num_threads as usize;
                                for _ in 0..ops_per_thread {
                                    // Allocate 64 bytes with 8-byte alignment
                                    let ptr = rt_arena_alloc(*arena_handle, 64, 8);
                                    black_box(ptr);
                                }
                            })
                        })
                        .collect();

                    for handle in handles {
                        handle.join().unwrap();
                    }

                    rt_arena_free(*arena_handle);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark TLS operations with varying thread counts
fn bench_tls_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("tls_operations");

    for num_threads in [1, 4, 8, 16] {
        group.throughput(Throughput::Elements(100_000));

        // Set/get workload
        group.bench_with_input(
            BenchmarkId::new("set_get", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let tls_handle = rt_tls_new();
                    let tls_handle = Arc::new(tls_handle);

                    let handles: Vec<_> = (0..num_threads)
                        .map(|thread_id| {
                            let tls_handle = Arc::clone(&tls_handle);
                            thread::spawn(move || {
                                let ops_per_thread = 100_000 / num_threads as usize;
                                let thread_key = thread_id as u64;
                                for i in 0..ops_per_thread {
                                    let value = RuntimeValue::from_int(i as i64);
                                    rt_tls_set(*tls_handle, thread_key, value);
                                    black_box(rt_tls_get(*tls_handle, thread_key));
                                }
                            })
                        })
                        .collect();

                    for handle in handles {
                        handle.join().unwrap();
                    }

                    rt_tls_free(*tls_handle);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_map_operations,
    bench_queue_operations,
    bench_stack_operations,
    bench_pool_operations,
    bench_arena_operations,
    bench_tls_operations
);
criterion_main!(benches);
