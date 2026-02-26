//! Parallel GPU Execution Engine
//!
//! This module provides parallel software execution that simulates GPU thread behavior,
//! allowing GPU kernels to run on the CPU with proper work group semantics.

use std::sync::{Arc, Barrier as SyncBarrier, Mutex};
use std::thread;

use crate::buffer::Buffer;
use crate::error::{GpuError, GpuResult};
use crate::intrinsics::WorkItemState;

/// Parallel execution configuration.
#[derive(Debug, Clone)]
pub struct ParallelConfig {
    /// Number of CPU threads to use.
    pub num_threads: usize,
    /// Whether to simulate warp/wavefront behavior.
    pub simulate_warps: bool,
    /// Warp/wavefront size for simulation.
    pub warp_size: u32,
}

impl Default for ParallelConfig {
    fn default() -> Self {
        ParallelConfig {
            num_threads: thread::available_parallelism().map(|p| p.get()).unwrap_or(4),
            simulate_warps: true,
            warp_size: 32,
        }
    }
}

impl ParallelConfig {
    /// Create a config with a specific number of threads.
    pub fn with_threads(num_threads: usize) -> Self {
        ParallelConfig {
            num_threads,
            ..Default::default()
        }
    }

    /// Create a single-threaded config (useful for debugging).
    pub fn single_threaded() -> Self {
        ParallelConfig {
            num_threads: 1,
            simulate_warps: false,
            warp_size: 1,
        }
    }
}

/// A parallel work group executor.
pub struct WorkGroupExecutor {
    config: ParallelConfig,
}

impl WorkGroupExecutor {
    /// Create a new executor with default config.
    pub fn new() -> Self {
        WorkGroupExecutor {
            config: ParallelConfig::default(),
        }
    }

    /// Create an executor with custom config.
    pub fn with_config(config: ParallelConfig) -> Self {
        WorkGroupExecutor { config }
    }

    /// Execute a kernel function across all work items.
    ///
    /// The kernel function receives the work item state and can access shared data.
    pub fn execute<F>(&self, global_size: [u32; 3], local_size: [u32; 3], kernel: F) -> GpuResult<()>
    where
        F: Fn(&WorkItemState) + Sync + Send,
    {
        let total_items = global_size[0] as usize * global_size[1] as usize * global_size[2] as usize;

        if total_items == 0 {
            return Ok(());
        }

        // Calculate number of work groups
        let num_groups = [
            global_size[0].div_ceil(local_size[0]),
            global_size[1].div_ceil(local_size[1]),
            global_size[2].div_ceil(local_size[2]),
        ];

        let total_groups = num_groups[0] as usize * num_groups[1] as usize * num_groups[2] as usize;

        // Distribute work groups across threads
        let kernel = Arc::new(kernel);
        let chunk_size = total_groups.div_ceil(self.config.num_threads);

        thread::scope(|s| {
            for thread_id in 0..self.config.num_threads {
                let start_group = thread_id * chunk_size;
                let end_group = ((thread_id + 1) * chunk_size).min(total_groups);

                if start_group >= total_groups {
                    break;
                }

                let kernel = Arc::clone(&kernel);

                s.spawn(move || {
                    for group_linear in start_group..end_group {
                        // Convert linear group ID to 3D
                        let group_id = [
                            (group_linear % num_groups[0] as usize) as u32,
                            ((group_linear / num_groups[0] as usize) % num_groups[1] as usize) as u32,
                            (group_linear / (num_groups[0] as usize * num_groups[1] as usize)) as u32,
                        ];

                        // Execute all work items in this work group
                        for lz in 0..local_size[2] {
                            for ly in 0..local_size[1] {
                                for lx in 0..local_size[0] {
                                    let local_id = [lx, ly, lz];
                                    let global_id = [
                                        group_id[0] * local_size[0] + lx,
                                        group_id[1] * local_size[1] + ly,
                                        group_id[2] * local_size[2] + lz,
                                    ];

                                    // Skip if out of bounds
                                    if global_id[0] >= global_size[0]
                                        || global_id[1] >= global_size[1]
                                        || global_id[2] >= global_size[2]
                                    {
                                        continue;
                                    }

                                    let state =
                                        WorkItemState::new(global_id, local_id, group_id, global_size, local_size);

                                    kernel(&state);
                                }
                            }
                        }
                    }
                });
            }
        });

        Ok(())
    }

    /// Execute a 1D kernel.
    pub fn execute_1d<F>(&self, global_size: u32, local_size: u32, kernel: F) -> GpuResult<()>
    where
        F: Fn(&WorkItemState) + Sync + Send,
    {
        self.execute([global_size, 1, 1], [local_size, 1, 1], kernel)
    }
}

impl Default for WorkGroupExecutor {
    fn default() -> Self {
        Self::new()
    }
}

/// Shared memory for work group operations.
///
/// This simulates GPU shared memory that is accessible to all threads
/// within a work group but private to that work group.
pub struct SharedMemory<T> {
    data: Vec<Mutex<T>>,
    size: usize,
}

impl<T: Clone + Default> SharedMemory<T> {
    /// Create a new shared memory region.
    pub fn new(size: usize) -> Self {
        let mut data = Vec::with_capacity(size);
        for _ in 0..size {
            data.push(Mutex::new(T::default()));
        }
        SharedMemory { data, size }
    }

    /// Get the size of the shared memory.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Check if the shared memory is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Read a value from shared memory.
    pub fn load(&self, index: usize) -> T {
        self.data[index].lock().unwrap().clone()
    }

    /// Write a value to shared memory.
    pub fn store(&self, index: usize, value: T) {
        *self.data[index].lock().unwrap() = value;
    }

    /// Atomic add (for numeric types).
    pub fn atomic_add(&self, index: usize, value: T) -> T
    where
        T: std::ops::AddAssign + Copy,
    {
        let mut guard = self.data[index].lock().unwrap();
        let old = *guard;
        *guard += value;
        old
    }
}

/// Work group barrier for synchronization.
///
/// This allows all threads in a work group to synchronize.
pub struct WorkGroupBarrier {
    barrier: SyncBarrier,
    group_size: usize,
}

impl WorkGroupBarrier {
    /// Create a new barrier for a work group.
    pub fn new(group_size: usize) -> Self {
        WorkGroupBarrier {
            barrier: SyncBarrier::new(group_size),
            group_size,
        }
    }

    /// Wait at the barrier.
    pub fn wait(&self) {
        self.barrier.wait();
    }

    /// Get the number of threads in the work group.
    pub fn group_size(&self) -> usize {
        self.group_size
    }
}

/// Execute a parallel reduction operation.
///
/// This performs a tree-reduction pattern commonly used in GPU computing.
pub fn parallel_reduce<T, F>(data: &[T], op: F) -> T
where
    T: Clone + Default + Send + Sync,
    F: Fn(&T, &T) -> T + Sync + Send,
{
    if data.is_empty() {
        return T::default();
    }

    if data.len() == 1 {
        return data[0].clone();
    }

    // Use parallel reduction with work stealing
    let num_threads = thread::available_parallelism().map(|p| p.get()).unwrap_or(4);

    let chunk_size = data.len().div_ceil(num_threads);
    let results: Arc<Mutex<Vec<T>>> = Arc::new(Mutex::new(Vec::with_capacity(num_threads)));

    thread::scope(|s| {
        for chunk in data.chunks(chunk_size) {
            let results = Arc::clone(&results);
            let op = &op;

            s.spawn(move || {
                // Local reduction
                let local_result = chunk.iter().skip(1).fold(chunk[0].clone(), |acc, x| op(&acc, x));
                results.lock().unwrap().push(local_result);
            });
        }
    });

    // Final reduction
    let final_results = results.lock().unwrap();
    final_results
        .iter()
        .skip(1)
        .fold(final_results[0].clone(), |acc, x| op(&acc, x))
}

/// Execute a parallel scan (prefix sum) operation.
///
/// This performs an inclusive scan using the Blelloch algorithm pattern.
pub fn parallel_scan<T, F>(data: &mut [T], op: F)
where
    T: Clone + Default + Send + Sync,
    F: Fn(&T, &T) -> T + Sync + Send,
{
    if data.len() <= 1 {
        return;
    }

    // Simple sequential scan for now
    // A full parallel implementation would use Blelloch's algorithm
    for i in 1..data.len() {
        let prev = data[i - 1].clone();
        data[i] = op(&prev, &data[i]);
    }
}

/// Execute a map operation in parallel.
pub fn parallel_map<T, U, F>(input: &Buffer<T>, output: &mut Buffer<U>, f: F) -> GpuResult<()>
where
    T: Clone + Default + Send + Sync,
    U: Clone + Default + Send + Sync,
    F: Fn(&T) -> U + Sync + Send,
{
    if input.len() != output.len() {
        return Err(GpuError::InvalidArgument(
            "Input and output buffer sizes must match".to_string(),
        ));
    }

    let executor = WorkGroupExecutor::new();
    let input_data = input.data();
    let output_data = Arc::new(Mutex::new(vec![U::default(); output.len()]));

    executor.execute_1d(input.len() as u32, 256, |state| {
        let idx = state.global_id[0] as usize;
        if idx < input_data.len() {
            let result = f(&input_data[idx]);
            output_data.lock().unwrap()[idx] = result;
        }
    })?;

    // Copy results back
    let results = output_data.lock().unwrap();
    output.upload(&results)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_work_group_executor_1d() {
        let executor = WorkGroupExecutor::new();
        let results = Arc::new(Mutex::new(vec![0u32; 100]));
        let results_clone = Arc::clone(&results);

        executor
            .execute_1d(100, 32, move |state| {
                let idx = state.global_id[0] as usize;
                results_clone.lock().unwrap()[idx] = idx as u32 * 2;
            })
            .unwrap();

        let final_results = results.lock().unwrap();
        for i in 0..100 {
            assert_eq!(final_results[i], i as u32 * 2);
        }
    }

    #[test]
    fn test_work_group_executor_2d() {
        let executor = WorkGroupExecutor::new();
        let results = Arc::new(Mutex::new(vec![vec![0u32; 8]; 8]));
        let results_clone = Arc::clone(&results);

        executor
            .execute([8, 8, 1], [4, 4, 1], move |state| {
                let x = state.global_id[0] as usize;
                let y = state.global_id[1] as usize;
                results_clone.lock().unwrap()[y][x] = (x + y * 8) as u32;
            })
            .unwrap();

        let final_results = results.lock().unwrap();
        for y in 0..8 {
            for x in 0..8 {
                assert_eq!(final_results[y][x], (x + y * 8) as u32);
            }
        }
    }

    #[test]
    fn test_shared_memory() {
        let shared = SharedMemory::<i32>::new(256);

        shared.store(0, 42);
        assert_eq!(shared.load(0), 42);

        let old = shared.atomic_add(0, 10);
        assert_eq!(old, 42);
        assert_eq!(shared.load(0), 52);
    }

    #[test]
    fn test_parallel_reduce_sum() {
        let data: Vec<i32> = (0..1000).collect();
        let sum = parallel_reduce(&data, |a, b| a + b);
        let expected: i32 = (0..1000).sum();
        assert_eq!(sum, expected);
    }

    #[test]
    fn test_parallel_reduce_max() {
        let data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
        let max = parallel_reduce(&data, |a, b| *a.max(b));
        assert_eq!(max, 9);
    }

    #[test]
    fn test_parallel_scan() {
        let mut data = vec![1, 2, 3, 4, 5];
        parallel_scan(&mut data, |a, b| a + b);
        assert_eq!(data, vec![1, 3, 6, 10, 15]);
    }

    #[test]
    fn test_single_threaded_config() {
        let config = ParallelConfig::single_threaded();
        let executor = WorkGroupExecutor::with_config(config);

        let results = Arc::new(Mutex::new(vec![0u32; 10]));
        let results_clone = Arc::clone(&results);

        executor
            .execute_1d(10, 5, move |state| {
                results_clone.lock().unwrap()[state.global_id[0] as usize] = state.global_id[0];
            })
            .unwrap();

        let final_results = results.lock().unwrap();
        for i in 0..10 {
            assert_eq!(final_results[i], i as u32);
        }
    }
}
