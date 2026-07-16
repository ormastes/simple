//! Minimal settlement stub executable.
//!
//! When built, this binary can have settlement data appended to it.
//! At runtime, it calls rt_settlement_main() to find and execute
//! the appended settlement data.

fn main() {
    // Link to the runtime's settlement_main function
    let exit_code = simple_runtime::loader::startup::settlement_main();
    std::process::exit(exit_code);
}

// The settlement stub links `simple-runtime` directly, so it must provide the
// canonical CLI argument hooks that generated native runtimes normally supply.
// Keep this tiny provider local to the stub; the full driver has its own copy.
static ARGS: std::sync::OnceLock<Vec<std::ffi::CString>> = std::sync::OnceLock::new();

fn args() -> &'static [std::ffi::CString] {
    ARGS.get_or_init(|| {
        std::env::args()
            .map(|arg| std::ffi::CString::new(arg).unwrap_or_default())
            .collect()
    })
}

#[no_mangle]
pub extern "C" fn spl_arg_count() -> i64 {
    args().len() as i64
}

#[no_mangle]
pub extern "C" fn spl_get_arg(index: i64) -> *const std::os::raw::c_char {
    if index < 0 {
        return std::ptr::null();
    }
    args()
        .get(index as usize)
        .map_or(std::ptr::null(), |arg| arg.as_ptr())
}
