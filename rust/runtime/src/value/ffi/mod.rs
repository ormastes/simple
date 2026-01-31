//! FFI (Foreign Function Interface) for RuntimeValue operations.
//!
//! This module provides C-compatible FFI functions for interacting with the Simple
//! runtime from compiled code. The module is organized into logical submodules:
//!
//! ## Phase 1: Core Value Operations ✅
//! - `value_ops` - Value creation, extraction, and type checking
//! - `memory` - Raw memory allocation and pointer conversion
//! - `equality` - Value equality comparison
//!
//! ## Phase 2: Hashing & Concurrency ✅
//! - `hash` - Hash functions (SHA1, SHA256, XXHash)
//! - `concurrent` - Concurrent data structures (Arena, Map, Queue, Stack, Pool, TLS)
//!
//! ## Phase 3: I/O & Runtime Services ✅
//! - `interpreter_bridge` - Interpreter call/eval handlers for hybrid execution
//! - `error_handling` - Runtime error reporting (function/method not found)
//! - `contracts` - Design by Contract checking (pre/post conditions, invariants)
//! - `io_capture` - Stdout/stderr capture and mock stdin for testing
//! - `io_print` - Print functions with capture support and stdin input
//!
//! ## Phase 4: Math Functions ✅
//! - `math` - Mathematical functions (trig, hyperbolic, logarithmic, power, rounding)
//!
//! ## Phase 5: Time & Timestamp Functions ✅
//! - `time` - Time functions and timestamp operations (current time, component extraction, arithmetic)
//!
//! ## Phase 6: File I/O & Path Operations ✅
//! - `file_io` - File system operations (read/write, copy, remove, stat, mmap, path manipulation)
//!
//! ## Phase 7: Environment & Process Operations ✅
//! - `env_process` - Environment variables, process execution, platform detection, coverage probes
//!
//! ## Phase 8: Atomic Operations ✅
//! - `atomic` - Atomic operations (AtomicBool, AtomicInt, AtomicFlag, Once)
//!
//! ## Phase 9: Synchronization Primitives ✅
//! - `sync` - Synchronization (Condvar, RwLock helpers, Thread-Local Storage, threading utilities)
//!
//! ## Phase 10A: Utility Functions ✅
//! - `utils` - Utilities (Base64 encode/decode, FNV hash)
//!
//! ## Phase 10B: PyTorch/ML Integration ✅
//! - `pytorch` - PyTorch operations (tensors, autograd, layers, optimizers, JIT, ONNX, distributed)
//!
//! ## Phase 11: Runtime Configuration ✅
//! - `config` - Runtime configuration (macro trace, debug mode)
//!
//! ## Phase 12: Regular Expressions ✅
//! - `regex` - Regular expression operations (match, find, capture, replace, split)
//!
//! ## Refactoring Complete! ✅
//! All FFI functions have been extracted from ffi_legacy.rs into organized, tested modules.
//!
//! All FFI functions use `#[no_mangle]` and `extern "C"` for C compatibility.

// Phase 1: Core value operations
pub mod equality;
pub mod memory;
pub mod value_ops;

// Phase 2: Hashing & concurrency
pub mod concurrent;
pub mod hash;

// Phase 3: I/O & runtime services
pub mod contracts;
pub mod error_handling;
pub mod interpreter_bridge;
pub mod io_capture;
pub mod io_print;

// Phase 4: Math functions
pub mod math;

// Phase 5: Time & timestamp functions
pub mod time;

// Phase 6: File I/O & path operations
pub mod file_io;

// Phase 7: Environment & process operations
pub mod env_process;

// Phase 8: Atomic operations
pub mod atomic;

// Phase 9: Synchronization primitives
pub mod sync;

// Phase 10A: Utility functions
pub mod utils;

// Phase 10B: PyTorch/ML integration
pub mod pytorch;

// Phase 11: Runtime configuration
pub mod config;

// Phase 12: Regular expressions
pub mod regex;

// Phase 13: Sandbox operations
pub mod sandbox;

// Phase 14: Random number generation
pub mod random;

// Phase 15: Resource registry for leak detection
pub mod resource_registry;

// Re-export all public FFI functions for backward compatibility
// Phase 1
pub use equality::*;
pub use memory::*;
pub use value_ops::*;

// Phase 2
pub use concurrent::*;
pub use hash::*;

// Phase 3
pub use contracts::*;
pub use error_handling::*;
pub use interpreter_bridge::*;
pub use io_capture::*;
pub use io_print::*;

// Phase 4
pub use math::*;

// Phase 5
pub use time::*;

// Phase 6
pub use file_io::*;

// Phase 7
pub use env_process::*;

// Phase 8
pub use atomic::*;

// Phase 9
pub use sync::*;

// Phase 10A
pub use utils::*;

// Phase 10B
pub use pytorch::*;

// Phase 11
pub use config::*;

// Phase 12
pub use regex::*;

// Phase 13
pub use sandbox::*;

// Phase 14
pub use random::*;

// Phase 15
pub use resource_registry::*;
