// FIXTURE — not compiled. PLANTED DEFECT, class 2:
// the compiler declares 4 params, the ONLY implementation takes 5, so the
// callee reads an uninitialised register for `recursive`. This is the
// rt_file_find shape.
#[no_mangle]
pub unsafe extern "C" fn rt_selftest_arity(
    dir_ptr: *const u8,
    dir_len: u64,
    pattern_ptr: *const u8,
    pattern_len: u64,
    recursive: bool,
) -> RuntimeValue {
    let _ = (dir_ptr, dir_len, pattern_ptr, pattern_len, recursive);
    RuntimeValue::from_int(0)
}
