//! Actual SDL engine execution through the Rust-owned native text/array ABI.
use simple_runtime::sdl_native_bridge::{rt_sdl_create_window, rt_sdl_present_rgba, rt_sdl2_last_error};
use simple_runtime::{rt_array_new, rt_array_push, rt_string_data, rt_string_len, rt_string_new};
use simple_runtime::value::RuntimeValue;

extern "C" {
    fn rt_sdl_init() -> i64;
    fn rt_sdl_destroy_window(handle: i64);
    fn rt_sdl_quit();
}

#[test]
fn sdl_runtime_owner_presents_nontrivial_pixels_and_rejects_wrong_values() {
    // A real software SDL surface, with no desktop/session requirement.
    let previous = std::env::var_os("SDL_VIDEODRIVER");
    std::env::set_var("SDL_VIDEODRIVER", "dummy");
    let initialized = unsafe { rt_sdl_init() };
    let error = rt_sdl2_last_error();
    let bytes = unsafe { std::slice::from_raw_parts(rt_string_data(error), rt_string_len(error) as usize) };
    assert_ne!(
        initialized,
        0,
        "real SDL2 dependency/init failed: {}",
        String::from_utf8_lossy(bytes)
    );
    let title = "窗口 α\0suffix".as_bytes();
    let title = rt_string_new(title.as_ptr(), title.len() as u64);
    let window = rt_sdl_create_window(title, 2, 1);
    assert_ne!(window, 0, "the owner string must reach a real SDL window");
    let pixels = rt_array_new(2);
    rt_array_push(pixels, RuntimeValue::from_int(0x123456ff));
    rt_array_push(pixels, RuntimeValue::from_int(0xfedcba80));
    assert!(rt_sdl_present_rgba(window, pixels, 2, 1));
    assert!(!rt_sdl_present_rgba(window, title, 2, 1));
    assert!(!rt_sdl_present_rgba(window, RuntimeValue::from_raw(0x12345679), 2, 1));
    assert!(!rt_sdl_present_rgba(window, pixels, 3, 1));
    assert_eq!(rt_sdl_create_window(pixels, 2, 1), 0);
    unsafe {
        rt_sdl_destroy_window(window);
        rt_sdl_quit();
    }
    match previous {
        Some(value) => std::env::set_var("SDL_VIDEODRIVER", value),
        None => std::env::remove_var("SDL_VIDEODRIVER"),
    }
}
