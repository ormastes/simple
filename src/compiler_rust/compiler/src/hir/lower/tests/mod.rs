// Common test helpers
use super::*;
use simple_parser::Parser;

/// Parse Simple source and lower to HIR
pub fn parse_and_lower(source: &str) -> LowerResult<HirModule> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    lower(&module)
}

// ---------------------------------------------------------------------------
// Test-binary link infra (NOT a regression test itself)
// ---------------------------------------------------------------------------
// `simple-runtime`'s cli_sffi.rs declares `spl_arg_count`/`spl_get_arg` as
// extern symbols normally supplied by Simple-generated Stage4 code (see fix
// 7a4cb1ab3d3, which added the equivalent provider to the `simple-driver`
// bin crate so plain `cargo build -p simple-driver --bin simple` links).
// `simple-compiler`'s OWN `--lib` test binary links `simple-runtime` too but
// has no such provider anywhere in its own closure, so without this it fails
// at link time with "undefined symbol: spl_arg_count" / "spl_get_arg" for
// EVERY test in this crate, regardless of which test triggers the link.
// `#[no_mangle]` symbols escape Rust's per-module name mangling, so defining
// them here (compiled only under `#[cfg(test)]` via `hir/lower/mod.rs`'s
// `mod tests;`) satisfies the whole binary's link exactly once.
#[no_mangle]
pub extern "C" fn spl_arg_count() -> i64 {
    std::env::args().count() as i64
}

#[no_mangle]
pub extern "C" fn spl_get_arg(index: i64) -> *const std::os::raw::c_char {
    use std::sync::OnceLock;
    static ARGS: OnceLock<Vec<std::ffi::CString>> = OnceLock::new();
    let args = ARGS.get_or_init(|| {
        std::env::args()
            .map(|a| std::ffi::CString::new(a).unwrap_or_default())
            .collect()
    });
    if index < 0 {
        return std::ptr::null();
    }
    args.get(index as usize).map(|a| a.as_ptr()).unwrap_or(std::ptr::null())
}

// Test modules
mod advanced; // Refactored into sub-modules (SIMD/GPU tests)
mod async_desugar_tests;
mod class_tests;
mod control_flow_tests;
mod expression_tests;
mod function_tests;
mod lifetime_tests;
mod seed_regression_tests;
