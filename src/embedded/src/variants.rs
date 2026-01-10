//! Runtime Variants for Constrained Environments
//!
//! This module provides different runtime configurations based on target constraints:
//! - `no-float`: No floating-point operations (soft-float or integer-only)
//! - `no-alloc`: No heap allocation (stack and static only)
//! - `no-thread`: No threading/concurrency primitives
//! - `no-gc`: No garbage collection (manual memory management)
//!
//! ## Preset Profiles
//!
//! - `minimal`: All restrictions (for smallest footprint)
//! - `embedded-tiny`: For targets with <16KB RAM
//! - `embedded-small`: For targets with <64KB RAM

/// Runtime variant configuration.
#[derive(Debug, Clone, Copy)]
pub struct VariantConfig {
    /// Floating-point support enabled.
    pub has_float: bool,
    /// Heap allocation enabled.
    pub has_alloc: bool,
    /// Threading support enabled.
    pub has_thread: bool,
    /// Garbage collection enabled.
    pub has_gc: bool,
    /// Maximum stack size (0 = unlimited).
    pub max_stack: usize,
    /// Maximum heap size (0 = no heap).
    pub max_heap: usize,
}

impl VariantConfig {
    /// Get the current variant configuration based on feature flags.
    pub const fn current() -> Self {
        Self {
            has_float: !cfg!(feature = "no-float"),
            has_alloc: !cfg!(feature = "no-alloc"),
            has_thread: !cfg!(feature = "no-thread"),
            has_gc: !cfg!(feature = "no-gc"),
            max_stack: 0,
            max_heap: 0,
        }
    }

    /// Minimal configuration (most restricted).
    pub const fn minimal() -> Self {
        Self {
            has_float: false,
            has_alloc: false,
            has_thread: false,
            has_gc: false,
            max_stack: 1024,
            max_heap: 0,
        }
    }

    /// Tiny embedded configuration (<16KB RAM).
    pub const fn tiny() -> Self {
        Self {
            has_float: false,
            has_alloc: false,
            has_thread: false,
            has_gc: false,
            max_stack: 2048,
            max_heap: 0,
        }
    }

    /// Small embedded configuration (<64KB RAM).
    pub const fn small() -> Self {
        Self {
            has_float: true,
            has_alloc: true,
            has_thread: false,
            has_gc: false,
            max_stack: 4096,
            max_heap: 8192,
        }
    }

    /// Standard embedded configuration.
    pub const fn standard() -> Self {
        Self {
            has_float: true,
            has_alloc: true,
            has_thread: true,
            has_gc: false,
            max_stack: 8192,
            max_heap: 32768,
        }
    }
}

// ============================================================================
// Integer-only math for no-float variant
// ============================================================================

/// Fixed-point number representation (Q16.16 format).
/// Used when floating-point is disabled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Fixed32(i32);

impl Fixed32 {
    /// Number of fractional bits.
    pub const FRAC_BITS: u32 = 16;
    /// Scale factor (2^16).
    pub const SCALE: i32 = 1 << Self::FRAC_BITS;

    /// Zero value.
    pub const ZERO: Self = Self(0);
    /// One value.
    pub const ONE: Self = Self(Self::SCALE);
    /// Minimum value.
    pub const MIN: Self = Self(i32::MIN);
    /// Maximum value.
    pub const MAX: Self = Self(i32::MAX);

    /// Create from integer.
    pub const fn from_int(n: i32) -> Self {
        Self(n << Self::FRAC_BITS)
    }

    /// Create from raw bits.
    pub const fn from_raw(bits: i32) -> Self {
        Self(bits)
    }

    /// Get raw bits.
    pub const fn to_raw(self) -> i32 {
        self.0
    }

    /// Convert to integer (truncates).
    pub const fn to_int(self) -> i32 {
        self.0 >> Self::FRAC_BITS
    }

    /// Add two fixed-point numbers.
    pub const fn add(self, other: Self) -> Self {
        Self(self.0.wrapping_add(other.0))
    }

    /// Subtract two fixed-point numbers.
    pub const fn sub(self, other: Self) -> Self {
        Self(self.0.wrapping_sub(other.0))
    }

    /// Multiply two fixed-point numbers.
    pub const fn mul(self, other: Self) -> Self {
        let result = (self.0 as i64 * other.0 as i64) >> Self::FRAC_BITS;
        Self(result as i32)
    }

    /// Divide two fixed-point numbers.
    pub const fn div(self, other: Self) -> Self {
        if other.0 == 0 {
            return Self::MAX; // Return max on divide by zero
        }
        let result = ((self.0 as i64) << Self::FRAC_BITS) / other.0 as i64;
        Self(result as i32)
    }

    /// Absolute value.
    pub const fn abs(self) -> Self {
        if self.0 < 0 {
            Self(-self.0)
        } else {
            self
        }
    }

    /// Negate.
    pub const fn neg(self) -> Self {
        Self(-self.0)
    }

    /// Check if negative.
    pub const fn is_negative(self) -> bool {
        self.0 < 0
    }

    /// Check if zero.
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }
}

// ============================================================================
// Static allocation for no-alloc variant
// ============================================================================

/// Static buffer for no-alloc environments.
/// Pre-allocated fixed-size buffer.
#[repr(C, align(8))]
pub struct StaticBuffer<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> Default for StaticBuffer<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> StaticBuffer<N> {
    /// Create a new empty static buffer.
    pub const fn new() -> Self {
        Self {
            data: [0; N],
            len: 0,
        }
    }

    /// Get buffer capacity.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Get current length.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Check if empty.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Check if full.
    pub const fn is_full(&self) -> bool {
        self.len >= N
    }

    /// Clear the buffer.
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Push a byte, returns false if full.
    pub fn push(&mut self, byte: u8) -> bool {
        if self.len < N {
            self.data[self.len] = byte;
            self.len += 1;
            true
        } else {
            false
        }
    }

    /// Pop a byte, returns None if empty.
    pub fn pop(&mut self) -> Option<u8> {
        if self.len > 0 {
            self.len -= 1;
            Some(self.data[self.len])
        } else {
            None
        }
    }

    /// Get slice of data.
    pub fn as_slice(&self) -> &[u8] {
        &self.data[..self.len]
    }

    /// Get mutable slice of data.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.data[..self.len]
    }

    /// Extend from slice, returns number of bytes copied.
    pub fn extend_from_slice(&mut self, slice: &[u8]) -> usize {
        let available = N - self.len;
        let to_copy = slice.len().min(available);
        self.data[self.len..self.len + to_copy].copy_from_slice(&slice[..to_copy]);
        self.len += to_copy;
        to_copy
    }
}

/// Static string buffer.
pub type StaticString<const N: usize> = StaticBuffer<N>;

/// Static vector (fixed capacity).
#[repr(C)]
pub struct StaticVec<T, const N: usize> {
    data: [core::mem::MaybeUninit<T>; N],
    len: usize,
}

impl<T, const N: usize> Default for StaticVec<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> StaticVec<T, N> {
    /// Create a new empty static vector.
    ///
    /// # Safety
    /// This creates uninitialized memory. The caller must ensure
    /// that elements are properly initialized before reading.
    #[inline]
    pub fn new() -> Self {
        Self {
            // Safety: MaybeUninit array doesn't require initialization
            data: unsafe {
                core::mem::MaybeUninit::<[core::mem::MaybeUninit<T>; N]>::uninit().assume_init()
            },
            len: 0,
        }
    }

    /// Get capacity.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Get length.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Check if empty.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Check if full.
    pub const fn is_full(&self) -> bool {
        self.len >= N
    }

    /// Clear the vector.
    pub fn clear(&mut self) {
        // Drop all elements
        for i in 0..self.len {
            unsafe {
                self.data[i].assume_init_drop();
            }
        }
        self.len = 0;
    }

    /// Push an element, returns Err with the element if full.
    pub fn push(&mut self, value: T) -> Result<(), T> {
        if self.len < N {
            self.data[self.len].write(value);
            self.len += 1;
            Ok(())
        } else {
            Err(value)
        }
    }

    /// Pop an element.
    pub fn pop(&mut self) -> Option<T> {
        if self.len > 0 {
            self.len -= 1;
            Some(unsafe { self.data[self.len].assume_init_read() })
        } else {
            None
        }
    }

    /// Get element by index.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            Some(unsafe { self.data[index].assume_init_ref() })
        } else {
            None
        }
    }

    /// Get mutable element by index.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            Some(unsafe { self.data[index].assume_init_mut() })
        } else {
            None
        }
    }

    /// Get slice.
    pub fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.data.as_ptr() as *const T, self.len) }
    }

    /// Get mutable slice.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.data.as_mut_ptr() as *mut T, self.len) }
    }
}

impl<T, const N: usize> Drop for StaticVec<T, N> {
    fn drop(&mut self) {
        self.clear();
    }
}

// ============================================================================
// Simple cooperative scheduling for no-thread variant
// ============================================================================

/// Task state for cooperative multitasking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskState {
    /// Task is ready to run.
    Ready,
    /// Task is running.
    Running,
    /// Task is waiting.
    Waiting,
    /// Task has completed.
    Done,
}

/// Simple task handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TaskId(pub u8);

/// Cooperative task entry.
pub struct CoopTask {
    /// Task ID.
    pub id: TaskId,
    /// Task state.
    pub state: TaskState,
    /// Task function pointer.
    pub func: fn() -> bool,
}

/// Simple cooperative scheduler (round-robin).
/// Maximum 8 tasks for minimal memory footprint.
pub struct CoopScheduler {
    tasks: [Option<CoopTask>; 8],
    current: usize,
    task_count: usize,
}

impl Default for CoopScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl CoopScheduler {
    /// Create a new scheduler.
    pub const fn new() -> Self {
        Self {
            tasks: [None, None, None, None, None, None, None, None],
            current: 0,
            task_count: 0,
        }
    }

    /// Add a task. Returns task ID or None if full.
    pub fn add_task(&mut self, func: fn() -> bool) -> Option<TaskId> {
        for i in 0..8 {
            if self.tasks[i].is_none() {
                let id = TaskId(i as u8);
                self.tasks[i] = Some(CoopTask {
                    id,
                    state: TaskState::Ready,
                    func,
                });
                self.task_count += 1;
                return Some(id);
            }
        }
        None
    }

    /// Remove a task by ID.
    pub fn remove_task(&mut self, id: TaskId) -> bool {
        let idx = id.0 as usize;
        if idx < 8 && self.tasks[idx].is_some() {
            self.tasks[idx] = None;
            self.task_count -= 1;
            true
        } else {
            false
        }
    }

    /// Run one scheduling round.
    /// Returns true if any task ran.
    pub fn tick(&mut self) -> bool {
        if self.task_count == 0 {
            return false;
        }

        let start = self.current;
        loop {
            if let Some(ref mut task) = self.tasks[self.current] {
                if task.state == TaskState::Ready {
                    task.state = TaskState::Running;
                    let done = (task.func)();
                    if done {
                        task.state = TaskState::Done;
                    } else {
                        task.state = TaskState::Ready;
                    }
                    self.current = (self.current + 1) % 8;
                    return true;
                }
            }
            self.current = (self.current + 1) % 8;
            if self.current == start {
                break;
            }
        }
        false
    }

    /// Run scheduler until all tasks complete.
    pub fn run(&mut self) {
        while self.task_count > 0 {
            self.tick();
            // Clean up completed tasks
            for i in 0..8 {
                if let Some(ref task) = self.tasks[i] {
                    if task.state == TaskState::Done {
                        self.tasks[i] = None;
                        self.task_count -= 1;
                    }
                }
            }
        }
    }

    /// Get number of active tasks.
    pub fn active_tasks(&self) -> usize {
        self.task_count
    }
}

// ============================================================================
// Manual memory management for no-gc variant
// ============================================================================

/// Memory pool for manual allocation.
/// Fixed-size blocks for predictable allocation.
pub struct MemoryPool<const BLOCK_SIZE: usize, const BLOCK_COUNT: usize> {
    memory: [[u8; BLOCK_SIZE]; BLOCK_COUNT],
    free_mask: u64, // Bitmap of free blocks (max 64 blocks)
}

impl<const BLOCK_SIZE: usize, const BLOCK_COUNT: usize> Default
    for MemoryPool<BLOCK_SIZE, BLOCK_COUNT>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const BLOCK_SIZE: usize, const BLOCK_COUNT: usize> MemoryPool<BLOCK_SIZE, BLOCK_COUNT> {
    /// Create a new memory pool.
    /// All blocks are initially free.
    pub const fn new() -> Self {
        assert!(BLOCK_COUNT <= 64, "Maximum 64 blocks supported");
        Self {
            memory: [[0; BLOCK_SIZE]; BLOCK_COUNT],
            free_mask: (1u64 << BLOCK_COUNT) - 1, // All bits set = all free
        }
    }

    /// Allocate a block. Returns None if no blocks available.
    pub fn alloc(&mut self) -> Option<*mut u8> {
        if self.free_mask == 0 {
            return None;
        }

        // Find first free block
        let idx = self.free_mask.trailing_zeros() as usize;
        if idx >= BLOCK_COUNT {
            return None;
        }

        // Mark as allocated
        self.free_mask &= !(1u64 << idx);

        Some(self.memory[idx].as_mut_ptr())
    }

    /// Free a block. Returns false if pointer is invalid.
    pub fn free(&mut self, ptr: *mut u8) -> bool {
        let base = self.memory.as_ptr() as usize;
        let ptr_addr = ptr as usize;

        if ptr_addr < base {
            return false;
        }

        let offset = ptr_addr - base;
        let idx = offset / BLOCK_SIZE;

        if idx >= BLOCK_COUNT || !offset.is_multiple_of(BLOCK_SIZE) {
            return false;
        }

        // Check if already free
        if self.free_mask & (1u64 << idx) != 0 {
            return false;
        }

        // Mark as free
        self.free_mask |= 1u64 << idx;
        true
    }

    /// Get number of free blocks.
    pub fn free_count(&self) -> usize {
        self.free_mask.count_ones() as usize
    }

    /// Get number of allocated blocks.
    pub fn used_count(&self) -> usize {
        BLOCK_COUNT - self.free_count()
    }

    /// Get block size.
    pub const fn block_size(&self) -> usize {
        BLOCK_SIZE
    }

    /// Get total capacity in bytes.
    pub const fn capacity(&self) -> usize {
        BLOCK_SIZE * BLOCK_COUNT
    }
}

/// Arena allocator for no-gc variant.
/// Allocates sequentially, frees all at once.
pub struct Arena<const SIZE: usize> {
    memory: [u8; SIZE],
    offset: usize,
}

impl<const SIZE: usize> Default for Arena<SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const SIZE: usize> Arena<SIZE> {
    /// Create a new arena.
    pub const fn new() -> Self {
        Self {
            memory: [0; SIZE],
            offset: 0,
        }
    }

    /// Allocate memory with alignment.
    pub fn alloc(&mut self, size: usize, align: usize) -> Option<*mut u8> {
        // Align offset
        let aligned_offset = (self.offset + align - 1) & !(align - 1);
        let new_offset = aligned_offset + size;

        if new_offset > SIZE {
            return None;
        }

        self.offset = new_offset;
        Some(unsafe { self.memory.as_mut_ptr().add(aligned_offset) })
    }

    /// Allocate typed value.
    pub fn alloc_val<T>(&mut self, value: T) -> Option<&mut T> {
        let ptr = self.alloc(core::mem::size_of::<T>(), core::mem::align_of::<T>())?;
        unsafe {
            core::ptr::write(ptr as *mut T, value);
            Some(&mut *(ptr as *mut T))
        }
    }

    /// Reset arena (free all allocations).
    pub fn reset(&mut self) {
        self.offset = 0;
    }

    /// Get bytes used.
    pub fn used(&self) -> usize {
        self.offset
    }

    /// Get bytes remaining.
    pub fn remaining(&self) -> usize {
        SIZE - self.offset
    }
}
