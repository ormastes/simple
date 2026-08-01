use simple_runtime as _;
use std::ffi::CString;

unsafe extern "C" {
    fn rt_fb_fill32(dst_addr: u64, pixel_count: u64, color: u64);
    fn rt_fb_blit32(
        dst_addr: u64,
        dst_stride_pixels: u64,
        src_addr: u64,
        src_stride_pixels: u64,
        copy_w: u64,
        copy_h: u64,
    );
    fn rt_engine2d_rocm_upload_pixels(dst: i64, pixels: i64, count: i64) -> i64;
    fn rt_engine2d_rocm_download_pixels(src: i64, pixels: i64, byte_size: i64) -> i64;
    fn rt_engine2d_rocm_upload_host_buf(dst: i64, host_buf: i64, byte_size: i64) -> i64;
    fn rt_signal_install(signal_num: i64) -> i64;
    fn rt_signal_check(signal_num: i64) -> i64;
    fn rt_atexit_install() -> i64;
    fn rt_atexit_check() -> i64;
    fn rt_remove(path: *const std::ffi::c_char) -> i64;
    fn copy_mem(dst: *mut u8, src: *const u8, n: i64) -> *mut u8;
}

#[test]
fn fills_packed_pixels_with_low_color_bits() {
    let mut pixels = [0_u32; 5];
    unsafe {
        rt_fb_fill32(pixels.as_mut_ptr() as u64, pixels.len() as u64, 0xfeed_cafe_1234_5678);
    }
    assert_eq!(pixels, [0x1234_5678; 5]);
}

#[test]
fn blits_rows_with_independent_pixel_strides() {
    let source = [1_u32, 2, 99, 3, 4, 99];
    let mut destination = [0_u32; 8];
    unsafe {
        rt_fb_blit32(destination.as_mut_ptr() as u64, 4, source.as_ptr() as u64, 3, 2, 2);
    }
    assert_eq!(destination, [1, 2, 0, 0, 3, 4, 0, 0]);
}

#[test]
fn overlapping_downward_blit_preserves_later_source_rows() {
    let mut pixels = [1_u32, 2, 3, 4, 5, 6];
    let source = pixels.as_ptr() as u64;
    let destination = unsafe { pixels.as_mut_ptr().add(2) } as u64;
    unsafe {
        rt_fb_blit32(destination, 2, source, 2, 2, 2);
    }
    assert_eq!(pixels, [1, 2, 1, 2, 3, 4]);
}

#[test]
fn unavailable_hosted_rocm_pixel_transport_fails_closed() {
    unsafe {
        assert_eq!(rt_engine2d_rocm_upload_pixels(1, 2, 3), -3);
        assert_eq!(rt_engine2d_rocm_download_pixels(1, 2, 3), -3);
        assert_eq!(rt_engine2d_rocm_upload_host_buf(1, 2, 3), -3);
    }
}

#[test]
fn hosted_signal_latches_validate_bounds_and_start_clear() {
    unsafe {
        assert_eq!(rt_signal_install(-1), 0);
        assert_eq!(rt_signal_install(32), 0);
        assert_eq!(rt_signal_check(-1), 0);
        assert_eq!(rt_signal_check(32), 0);
        assert_eq!(rt_atexit_check(), 0);
        assert_eq!(rt_atexit_install(), 1);
        assert_eq!(rt_atexit_install(), 1);
    }
}

#[test]
fn hosted_remove_deletes_files_and_empty_directories() {
    let root = std::env::temp_dir().join(format!("simple-hosted-remove-{}", std::process::id()));
    let file = root.join("file.txt");
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir(&root).expect("create hosted remove test directory");
    std::fs::write(&file, b"remove me").expect("create hosted remove test file");

    let file_path = CString::new(file.to_string_lossy().as_bytes()).expect("file path CString");
    let root_path = CString::new(root.to_string_lossy().as_bytes()).expect("root path CString");
    unsafe {
        assert_eq!(rt_remove(file_path.as_ptr()), 0);
        assert_eq!(rt_remove(root_path.as_ptr()), 0);
        assert!(rt_remove(root_path.as_ptr()) < 0);
    }
    assert!(!file.exists());
    assert!(!root.exists());
}

#[test]
fn hosted_copy_mem_forwards_to_the_bounded_memory_copy_owner() {
    let source = [10_u8, 20, 30, 40];
    let mut destination = [0xaa_u8; 6];
    let copied = unsafe { copy_mem(destination.as_mut_ptr().add(1), source.as_ptr(), 4) };

    assert_eq!(copied, unsafe { destination.as_mut_ptr().add(1) });
    assert_eq!(destination, [0xaa, 10, 20, 30, 40, 0xaa]);
}
