//! WebAssembly Runtime for Simple Language
//!
//! This crate provides WASM execution capabilities using Wasmer runtime.
//! It allows executing compiled WASM modules with WASI support and SFFI
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

// Not gated on `wasm`: everything in this module that needs wasmer (the
// `initialize` bootstrap and `CapturingPipes`) carries its own `cfg`. The
// capability table, the policy parser and `validate_capabilities` are plain
// data logic, and gating them behind `wasm` meant the security enforcement
// could not be built or tested without the full wasmer stack.
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

// `__rust_probestack` for the `wasm` feature (wasmerio/wasmer#3857).
//
// This lives here, next to the wasmer dependency, and deliberately not in the
// `driver` crate where it started. An integration test (or any other consumer)
// that links `wasmer` without also linking `simple-driver` gets `wasmer-vm` and
// therefore the undefined reference, but not the definition:
//
//     rust-lld: error: undefined symbol: __rust_probestack
//     >>> referenced by wasmer_vm-....rcgu.o:(wasmer_vm_probestack)
//
// Defining it in the crate that owns the dependency means everything that pulls
// in wasmer resolves it, which is the only placement that is actually correct.
//
// Why the symbol is missing at all: `wasmer-vm` declares
// `extern "C" { fn __rust_probestack(); }` and publishes it as
// `LibCall::Probestack`, the routine cranelift-compiled *guest* code calls when a
// wasm frame exceeds one page. Rust used to export it unmangled from
// `compiler_builtins`; since ~1.79 it is emitted into the mangled `__rustc`
// namespace (`_RNv...___rustc17___rust_probestack`) instead, so wasmer 3.1's
// request for the legacy name goes unresolved on modern stable.
//
// It is provided for real rather than stubbed. A probestack exists precisely so a
// frame larger than the guard page cannot leap over it; a no-op turns guest stack
// overflow into memory corruption — the Stack Clash class of bug that wasmer's own
// `probestack.rs` header warns about, in a sandbox runtime. Body is the ELF x86_64
// routine from `compiler_builtins`: frame size arrives in `%rax`, every page
// between `%rsp+8` and `%rsp+8-%rax` is touched, and neither `%rsp` nor `%rax` is
// modified on return.
//
// x86_64-unix only, on purpose. `wasmer-vm` references this symbol only on
// non-Windows x86/x86_64; other architectures get its own `empty_probestack`.
// Leaving 32-bit x86 undefined makes it fail loudly at link time rather than
// quietly reintroducing the no-op hazard.
#[cfg(all(feature = "wasm", target_arch = "x86_64", unix))]
core::arch::global_asm!(
    "
    .pushsection .text.__rust_probestack
    .globl __rust_probestack
    .type  __rust_probestack, @function
    .hidden __rust_probestack
__rust_probestack:
    .cfi_startproc
    pushq  %rbp
    .cfi_adjust_cfa_offset 8
    .cfi_offset %rbp, -16
    movq   %rsp, %rbp
    .cfi_def_cfa_register %rbp

    mov    %rax,%r11

    cmp    $0x1000,%r11
    jna    3f
2:
    sub    $0x1000,%rsp
    test   %rsp,8(%rsp)
    sub    $0x1000,%r11
    cmp    $0x1000,%r11
    ja     2b

3:
    sub    %r11,%rsp
    test   %rsp,8(%rsp)

    add    %rax,%rsp

    leave
    .cfi_def_cfa_register %rsp
    .cfi_adjust_cfa_offset -8
    ret
    .cfi_endproc
    .size __rust_probestack, . - __rust_probestack
    .popsection
    ",
    options(att_syntax)
);

/// Re-exported so callers can drive `WasiConfig::build_wasi_env` — the seam where
/// capability enforcement actually runs — without adding their own `wasmer`
/// dependency and risking a version skew against the one enforcement runs on.
///
/// The enforcement regression tests need this: asserting on
/// `validate_capabilities` alone cannot tell whether it is still *called*, and a
/// check nothing calls is the failure mode this whole area keeps reproducing.
#[cfg(feature = "wasm")]
pub use wasmer;

pub use wasi_env::{declared_sandbox_names, WasiCapabilityTable, WasiConfig};

#[cfg(feature = "wasm")]
pub use wasi_env::CapturingPipes;

#[cfg(feature = "wasm")]
pub use bridge::{from_wasm_value, to_wasm_value};

#[cfg(feature = "wasm")]
pub use cache::ModuleCache;

pub use browser_mock::{BrowserMock, BrowserVerify, ConsoleMethod, DomElement, FetchResponse};
