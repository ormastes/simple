//! Rust provider delegates to the same canonical C owner as the native product.
//! No second token table and no raw-descriptor retry implementation.
extern "C" {
    fn spl_c_file_lock_owned_acquire_v2(path: *const u8, len: u64, timeout: i64) -> i64;
    fn spl_c_file_lock_owned_state_v2(token: i64) -> i64;
    fn spl_c_file_lock_owned_release_v2(token: i64) -> i64;
}
#[no_mangle]
pub unsafe extern "C" fn rt_file_lock_owned_acquire_v2(path: *const u8, len: u64, timeout: i64) -> i64 {
    spl_c_file_lock_owned_acquire_v2(path, len, timeout)
}
#[no_mangle]
pub unsafe extern "C" fn rt_file_lock_owned_state_v2(token: i64) -> i64 {
    spl_c_file_lock_owned_state_v2(token)
}
#[no_mangle]
pub unsafe extern "C" fn rt_file_lock_owned_release_v2(token: i64) -> i64 {
    spl_c_file_lock_owned_release_v2(token)
}
