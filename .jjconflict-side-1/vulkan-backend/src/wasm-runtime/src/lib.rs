//! WebAssembly Runtime for Simple Language
//!
//! This crate provides WASM execution capabilities using Wasmer runtime.
//! It allows executing compiled WASM modules with WASI support and FFI
//! bridges to Simple's RuntimeValue system.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────┐
//! │  WASM Binary    │
//! │  (.wasm file)   │
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │  WasmRunner     │  ← Module loading & caching
//! └────────┬────────┘
//!          │
//!     ┌────┴────┐
//!     │         │
//!     ▼         ▼
//! ┌─────┐   ┌──────┐
//! │WASI │   │Bridge│  ← RuntimeValue ↔ WasmValue
//! │ Env │   │      │
//! └─────┘   └──────┘
//! ```
//!
//! # Features
//!
//! - **wasm**: Enable Wasmer-based WASM execution (requires `wasmer` dependency)
//!
//! # Example
//!
//! ```ignore
//! use simple_wasm_runtime::{WasmRunner, WasiConfig};
//!
//! // Create runner with WASI support
//! let config = WasiConfig::new()
//!     .with_args(&["arg1", "arg2"])
//!     .with_env("KEY", "VALUE");
//!
//! let runner = WasmRunner::new(config)?;
//!
//! // Load and execute WASM module
//! let result = runner.run_wasm_file("module.wasm", "main")?;
//! ```

pub mod error;

#[cfg(feature = "wasm")]
pub mod runner;

#[cfg(feature = "wasm")]
pub mod wasi_env;

#[cfg(feature = "wasm")]
pub mod bridge;

#[cfg(feature = "wasm")]
pub mod cache;

pub mod browser_mock;

// Re-export main types
pub use error::{WasmError, WasmResult};

#[cfg(feature = "wasm")]
pub use runner::WasmRunner;

#[cfg(feature = "wasm")]
pub use wasi_env::{WasiConfig, CapturingPipes};

#[cfg(feature = "wasm")]
pub use bridge::{to_wasm_value, from_wasm_value};

#[cfg(feature = "wasm")]
pub use cache::ModuleCache;

pub use browser_mock::{
    BrowserMock, BrowserVerify, ConsoleMethod, DomElement, FetchResponse,
};
