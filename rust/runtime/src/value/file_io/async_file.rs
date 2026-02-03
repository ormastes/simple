//! Async file loading operations - Background file I/O with thread pool
//!
//! Provides native implementations for:
//! - Async file handle creation and management
//! - Background file loading with mmap
//! - Progressive prefaulting for large files
//! - Thread pool for concurrent file operations

use crate::value::RuntimeValue;
use parking_lot::RwLock;
use std::sync::mpsc::{channel, Sender};
use std::sync::Arc;
use std::thread::{self, JoinHandle};

/// Memory-mapped region handle
///
/// Represents a single memory-mapped region with its base pointer and size.
/// Used to track active mappings and facilitate cleanup.
#[derive(Clone, Copy)]
pub struct MmapRegion {
    pub ptr: *mut u8,
    pub size: usize,
}

// SAFETY: MmapRegion only stores raw pointers from mmap which are thread-safe
// The pointer itself can be shared across threads as it points to memory-mapped pages
unsafe impl Send for MmapRegion {}
unsafe impl Sync for MmapRegion {}

/// File loading state for async operations
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileLoadState {
    Pending = 0,
    Loading = 1,
    Ready = 2,
    Failed = 3,
}

/// Async file handle for background loading
#[derive(Clone)]
pub struct AsyncFileHandle {
    path: String,
    state: Arc<RwLock<FileLoadState>>,
    region: Arc<RwLock<Option<MmapRegion>>>,
    error: Arc<RwLock<Option<String>>>,
    mode: i32,      // Open mode flags
    prefault: bool, // Enable progressive prefaulting
}

impl AsyncFileHandle {
    /// Create a new async file handle
    pub fn new(path: String, mode: i32, prefault: bool) -> Self {
        AsyncFileHandle {
            path,
            state: Arc::new(RwLock::new(FileLoadState::Pending)),
            region: Arc::new(RwLock::new(None)),
            error: Arc::new(RwLock::new(None)),
            mode,
            prefault,
        }
    }

    /// Start loading the file in background
    pub fn start_loading(&self) {
        let path = self.path.clone();
        let state = self.state.clone();
        let region = self.region.clone();
        let error = self.error.clone();
        let mode = self.mode;
        let prefault = self.prefault;

        // Submit to thread pool
        ASYNC_FILE_POOL.submit(move || {
            // Mark as loading
            *state.write() = FileLoadState::Loading;

            // Perform the actual file loading
            match load_file_mmap(&path, mode, prefault) {
                Ok(mmap_region) => {
                    *region.write() = Some(mmap_region);
                    *state.write() = FileLoadState::Ready;
                }
                Err(e) => {
                    *error.write() = Some(e);
                    *state.write() = FileLoadState::Failed;
                }
            }
        });
    }

    /// Check if file is ready (non-blocking)
    pub fn is_ready(&self) -> bool {
        *self.state.read() == FileLoadState::Ready
    }

    /// Check if loading failed
    pub fn is_failed(&self) -> bool {
        *self.state.read() == FileLoadState::Failed
    }

    /// Get current state
    pub fn get_state(&self) -> FileLoadState {
        *self.state.read()
    }

    /// Wait for loading to complete (blocking)
    pub fn wait(&self) -> Result<MmapRegion, String> {
        // Spin-wait until ready or failed
        loop {
            let state = *self.state.read();
            match state {
                FileLoadState::Ready => {
                    let region = self.region.read();
                    if let Some(r) = region.as_ref() {
                        return Ok(MmapRegion {
                            ptr: r.ptr,
                            size: r.size,
                        });
                    } else {
                        return Err("Region not available".to_string());
                    }
                }
                FileLoadState::Failed => {
                    let error = self.error.read();
                    return Err(error.clone().unwrap_or_else(|| "Unknown error".to_string()));
                }
                FileLoadState::Pending | FileLoadState::Loading => {
                    // Yield to avoid busy-waiting
                    std::thread::yield_now();
                    std::thread::sleep(std::time::Duration::from_micros(100));
                }
            }
        }
    }
}

/// Worker thread pool for async file operations
struct AsyncFileThreadPool {
    workers: Vec<JoinHandle<()>>,
    sender: Sender<Box<dyn FnOnce() + Send>>,
}

impl AsyncFileThreadPool {
    /// Create a new thread pool with the specified number of workers
    fn new(num_workers: usize) -> Self {
        let (sender, receiver) = channel::<Box<dyn FnOnce() + Send>>();
        let receiver = Arc::new(parking_lot::Mutex::new(receiver));

        let mut workers = Vec::with_capacity(num_workers);

        for id in 0..num_workers {
            let receiver = receiver.clone();
            let handle = thread::Builder::new()
                .name(format!("async-file-worker-{}", id))
                .spawn(move || {
                    loop {
                        let task = {
                            let lock = receiver.lock();
                            lock.recv()
                        };

                        match task {
                            Ok(task) => {
                                task();
                            }
                            Err(_) => {
                                // Channel closed, exit worker
                                break;
                            }
                        }
                    }
                })
                .expect("Failed to spawn worker thread");

            workers.push(handle);
        }

        AsyncFileThreadPool { workers, sender }
    }

    /// Submit a task to the thread pool
    fn submit<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.sender
            .send(Box::new(task))
            .expect("Failed to send task to thread pool");
    }
}

// Global thread pool for async file operations (lazy initialization)
lazy_static::lazy_static! {
    static ref ASYNC_FILE_POOL: AsyncFileThreadPool = {
        // Use syscall instead of num_cpus crate
        let cpu_count = unsafe { crate::syscalls_ffi::rt_system_cpu_count() as usize };
        let num_workers = cpu_count.max(4);
        AsyncFileThreadPool::new(num_workers)
    };
}

// Global handle registry for async file handles
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};

lazy_static::lazy_static! {
    static ref ASYNC_FILE_REGISTRY: Arc<RwLock<HashMap<i64, AsyncFileHandle>>> = {
        Arc::new(RwLock::new(HashMap::new()))
    };
}

static NEXT_HANDLE_ID: AtomicI64 = AtomicI64::new(1);

/// Extract a string from a RuntimeValue
fn runtime_value_to_string(value: RuntimeValue) -> Option<String> {
    if !value.is_heap() {
        return None;
    }

    unsafe {
        let ptr = value.as_heap_ptr();
        use crate::value::heap::HeapObjectType;

        if (*ptr).object_type != HeapObjectType::String {
            return None;
        }

        // RuntimeString has an as_bytes() method
        use crate::value::RuntimeString;
        let string_ptr = ptr as *const RuntimeString;
        let bytes = (*string_ptr).as_bytes();

        String::from_utf8(bytes.to_vec()).ok()
    }
}

/// Load a file using mmap (blocking operation)
///
/// This performs a blocking file load operation suitable for thread pool execution.
/// The function:
/// 1. Opens the file using platform-specific APIs
/// 2. Gets the file size
/// 3. Creates a memory-mapped region
/// 4. Optionally performs progressive prefaulting
/// 5. Closes the file descriptor (mmap keeps reference)
fn load_file_mmap(path: &str, mode: i32, prefault: bool) -> Result<MmapRegion, String> {
    // Note: These FFI functions are defined in the parent mod.rs module
    extern "C" {
        fn sys_file_size(fd: i32) -> i64;
        fn sys_mmap(addr: i64, length: u64, prot: i32, flags: i32, fd: i32, offset: u64) -> i64;
        fn sys_close(fd: i32) -> i32;
        fn sys_madvise(addr: i64, length: u64, advice: i32) -> i32;
    }

    // Open file
    let fd = unsafe {
        #[cfg(target_family = "unix")]
        {
            use std::ffi::CString;
            let c_path = CString::new(path).map_err(|e| format!("Invalid path: {}", e))?;
            libc::open(c_path.as_ptr(), mode)
        }
        #[cfg(target_family = "windows")]
        {
            use windows_sys::Win32::Foundation::INVALID_HANDLE_VALUE;
            use windows_sys::Win32::Storage::FileSystem::{CreateFileA, FILE_ATTRIBUTE_NORMAL, OPEN_EXISTING};

            let access = if mode & 0x1 != 0 { 0x80000000 } else { 0 }  // GENERIC_READ
                       | if mode & 0x2 != 0 { 0x40000000 } else { 0 }; // GENERIC_WRITE

            let handle = CreateFileA(
                path.as_ptr(),
                access,
                0x1 | 0x2, // FILE_SHARE_READ | FILE_SHARE_WRITE
                std::ptr::null(),
                OPEN_EXISTING,
                FILE_ATTRIBUTE_NORMAL,
                0,
            );

            if handle == INVALID_HANDLE_VALUE as isize {
                return Err(format!("Failed to open file: {}", path));
            }
            handle as i32
        }
    };

    if fd < 0 {
        return Err(format!("Failed to open file: {}", path));
    }

    // Get file size
    let file_size = unsafe { sys_file_size(fd) };
    if file_size < 0 {
        unsafe {
            sys_close(fd);
        }
        return Err("Failed to get file size".to_string());
    }

    // Create mmap
    let mmap_ptr = unsafe {
        sys_mmap(
            0, // addr: let kernel choose
            file_size as u64,
            1, // prot: PROT_READ
            2, // flags: MAP_PRIVATE
            fd,
            0, // offset
        )
    };

    if mmap_ptr < 0 {
        unsafe {
            sys_close(fd);
        }
        return Err("mmap failed".to_string());
    }

    // Progressive prefaulting if enabled
    if prefault {
        progressive_prefault(mmap_ptr as *mut u8, file_size as usize);
    }

    // Close fd (mmap keeps reference)
    unsafe {
        sys_close(fd);
    }

    Ok(MmapRegion {
        ptr: mmap_ptr as *mut u8,
        size: file_size as usize,
    })
}

/// Progressive prefaulting - gradually fault in pages (#1769)
///
/// This uses madvise WILLNEED to hint the kernel to load pages in the background.
/// Pages are loaded in 4MB chunks with small delays to avoid overwhelming the system.
fn progressive_prefault(ptr: *mut u8, size: usize) {
    extern "C" {
        fn sys_madvise(addr: i64, length: u64, advice: i32) -> i32;
    }

    const CHUNK_SIZE: usize = 4 * 1024 * 1024; // 4MB chunks
    const PREFAULT_ADVICE: i32 = 4; // MADV_WILLNEED

    let mut offset = 0;
    while offset < size {
        let chunk_size = std::cmp::min(CHUNK_SIZE, size - offset);

        unsafe {
            let chunk_ptr = ptr.add(offset);
            let _ = sys_madvise(chunk_ptr as i64, chunk_size as u64, PREFAULT_ADVICE);
        }

        offset += chunk_size;

        // Small delay to avoid overwhelming the system
        std::thread::sleep(std::time::Duration::from_micros(100));
    }
}

// =============================================================================
// Async File Handle FFI Functions
// =============================================================================

/// Create a new async file handle
///
/// # Arguments
/// * `path` - RuntimeValue containing the file path (String)
/// * `mode` - Open mode flags
/// * `prefault` - Enable progressive prefaulting (bool)
///
/// # Returns
/// Handle ID (as i64) for the async file handle
#[no_mangle]
pub extern "C" fn native_async_file_create(path: RuntimeValue, mode: i32, prefault: i32) -> i64 {
    // Extract string from RuntimeValue
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => {
            eprintln!("Error: Failed to extract string from RuntimeValue");
            return 0;
        }
    };

    let handle = AsyncFileHandle::new(path_str, mode, prefault != 0);

    // Generate new handle ID
    let handle_id = NEXT_HANDLE_ID.fetch_add(1, Ordering::SeqCst);

    // Store handle in registry
    ASYNC_FILE_REGISTRY.write().insert(handle_id, handle);

    handle_id
}

/// Start loading a file asynchronously
///
/// # Arguments
/// * `handle_id` - ID of the async file handle returned by native_async_file_create
#[no_mangle]
pub extern "C" fn native_async_file_start_loading(handle_id: i64) {
    if let Some(handle) = ASYNC_FILE_REGISTRY.read().get(&handle_id) {
        handle.start_loading();
    } else {
        eprintln!("Error: Invalid async file handle ID: {}", handle_id);
    }
}

/// Check if async file is ready (non-blocking)
///
/// # Arguments
/// * `handle_id` - ID of the async file handle
///
/// # Returns
/// 1 if ready, 0 otherwise
#[no_mangle]
pub extern "C" fn native_async_file_is_ready(handle_id: i64) -> i32 {
    if let Some(handle) = ASYNC_FILE_REGISTRY.read().get(&handle_id) {
        if handle.is_ready() {
            1
        } else {
            0
        }
    } else {
        0 // Invalid handle
    }
}

/// Get async file loading state
///
/// # Arguments
/// * `handle_id` - ID of the async file handle
///
/// # Returns
/// FileLoadState value (0=Pending, 1=Loading, 2=Ready, 3=Failed)
#[no_mangle]
pub extern "C" fn native_async_file_get_state(handle_id: i64) -> i32 {
    if let Some(handle) = ASYNC_FILE_REGISTRY.read().get(&handle_id) {
        handle.get_state() as i32
    } else {
        FileLoadState::Failed as i32 // Invalid handle = failed state
    }
}

/// Wait for async file to load (blocking)
///
/// # Arguments
/// * `handle_id` - ID of the async file handle
///
/// # Returns
/// RuntimeValue containing the MmapRegion pointer or error code (0 on error)
#[no_mangle]
pub extern "C" fn native_async_file_wait(handle_id: i64) -> RuntimeValue {
    let handle = match ASYNC_FILE_REGISTRY.read().get(&handle_id).cloned() {
        Some(h) => h,
        None => {
            eprintln!("Error: Invalid async file handle ID: {}", handle_id);
            return RuntimeValue::from_int(0);
        }
    };

    // Wait for completion
    match handle.wait() {
        Ok(region) => {
            // Return pointer to mmap region as an integer
            // The caller should interpret this as a pointer to memory-mapped data
            RuntimeValue::from_int(region.ptr as i64)
        }
        Err(e) => {
            eprintln!("Error loading file: {}", e);
            RuntimeValue::from_int(0)
        }
    }
}

// =============================================================================
// Async Primitives
// =============================================================================

/// Yield control back to async runtime
///
/// This is used for cooperative multitasking when busy-waiting.
/// In a real implementation, this would yield to the async runtime.
/// Currently hints to the scheduler to give other threads a chance.
#[no_mangle]
pub extern "C" fn async_yield() {
    std::thread::yield_now();
}

#[cfg(test)]
#[path = "async_file_tests.rs"]
mod tests;
