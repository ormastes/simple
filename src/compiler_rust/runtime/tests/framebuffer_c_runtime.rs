use simple_runtime as _;

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
