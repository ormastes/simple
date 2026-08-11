// FIXTURE — not compiled. Definition that AGREES with good_spec.rs.
#[no_mangle]
pub unsafe extern "C" fn rt_selftest_ok_rs(
    ptr: *const u8,
    len: u64,
    flags: i64,
) -> RuntimeValue {
    let _ = (ptr, len, flags);
    RuntimeValue::from_int(0)
}
