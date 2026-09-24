//! Rust ABI aliases for the descriptor-pinned C file-view provider.
//!
//! The C implementation remains the behavioral authority. `native_all`
//! compiles it under private `spl_c_*` symbols and these wrappers own the
//! public ABI, giving both runtime lanes an explicit, collision-free binding.

extern "C" {
    fn spl_c_file_view_open_beneath_no_follow_v1(root: i64, path: i64) -> i64;
    fn spl_c_file_view_mapping_supported_v1(handle: i64) -> i8;
    fn spl_c_file_view_map_copy_v1(handle: i64, offset: u64, length: u64) -> i64;
    fn spl_c_file_view_pread_exact_v1(handle: i64, offset: u64, length: u64) -> i64;
    fn spl_c_file_view_prefetch_v1(handle: i64, offset: u64, length: u64) -> i8;
    fn spl_c_file_view_device_v1(handle: i64) -> i64;
    fn spl_c_file_view_inode_v1(handle: i64) -> i64;
    fn spl_c_file_view_size_v1(handle: i64) -> i64;
    fn spl_c_file_view_close_v1(handle: i64) -> i8;
    fn spl_c_pinned_archive_open_beneath_v1(root: i64, path: i64) -> i64;
    fn spl_c_pinned_archive_device_v1(handle: i64) -> i64;
    fn spl_c_pinned_archive_inode_v1(handle: i64) -> i64;
    fn spl_c_pinned_archive_size_v1(handle: i64) -> i64;
    fn spl_c_pinned_archive_close_v1(handle: i64) -> i8;
}

#[no_mangle]
pub extern "C" fn rt_file_view_open_beneath_no_follow_v1(root: i64, path: i64) -> i64 {
    unsafe { spl_c_file_view_open_beneath_no_follow_v1(root, path) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_mapping_supported_v1(handle: i64) -> i8 {
    unsafe { spl_c_file_view_mapping_supported_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_map_copy_v1(handle: i64, offset: u64, length: u64) -> i64 {
    unsafe { spl_c_file_view_map_copy_v1(handle, offset, length) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_pread_exact_v1(handle: i64, offset: u64, length: u64) -> i64 {
    unsafe { spl_c_file_view_pread_exact_v1(handle, offset, length) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_prefetch_v1(handle: i64, offset: u64, length: u64) -> i8 {
    unsafe { spl_c_file_view_prefetch_v1(handle, offset, length) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_device_v1(handle: i64) -> i64 {
    unsafe { spl_c_file_view_device_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_inode_v1(handle: i64) -> i64 {
    unsafe { spl_c_file_view_inode_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_size_v1(handle: i64) -> i64 {
    unsafe { spl_c_file_view_size_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_file_view_close_v1(handle: i64) -> i8 {
    unsafe { spl_c_file_view_close_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_pinned_archive_open_beneath_v1(root: i64, path: i64) -> i64 {
    unsafe { spl_c_pinned_archive_open_beneath_v1(root, path) }
}

#[no_mangle]
pub extern "C" fn rt_pinned_archive_device_v1(handle: i64) -> i64 {
    unsafe { spl_c_pinned_archive_device_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_pinned_archive_inode_v1(handle: i64) -> i64 {
    unsafe { spl_c_pinned_archive_inode_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_pinned_archive_size_v1(handle: i64) -> i64 {
    unsafe { spl_c_pinned_archive_size_v1(handle) }
}

#[no_mangle]
pub extern "C" fn rt_pinned_archive_close_v1(handle: i64) -> i8 {
    unsafe { spl_c_pinned_archive_close_v1(handle) }
}
