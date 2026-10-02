//! Rust ABI alias for the descriptor-pinned C fd-stat provider.

extern "C" {
    fn spl_c_fd_stat_snapshot_v1(descriptor: i64, out_addr: i64, out_bytes: i64) -> i64;
}

#[no_mangle]
pub extern "C" fn rt_fd_stat_snapshot_v1(descriptor: i64, out_addr: i64, out_bytes: i64) -> i64 {
    unsafe { spl_c_fd_stat_snapshot_v1(descriptor, out_addr, out_bytes) }
}
