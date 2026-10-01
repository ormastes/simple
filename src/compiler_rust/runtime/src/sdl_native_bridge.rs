//! Rust-owned text and array boundary for the shared SDL2 C engine.
//! Scalars and window handles retain the engine ABI. Borrowed C strings and
//! unboxed pixels are temporary views, never Rust heap headers cast to C ones.

use std::ffi::{c_char, CStr, CString};

use crate::{rt_string_data, rt_string_len, rt_string_new, RuntimeArray};
use crate::value::heap::HeapObjectType;
use crate::value::RuntimeValue;

extern "C" {
    fn spl_sdl2_create_window_cstr(title: *const c_char, width: i64, height: i64) -> i64;
    fn spl_sdl2_set_window_title_cstr(handle: i64, title: *const c_char) -> bool;
    fn spl_sdl2_event_text_cstr() -> *const c_char;
    fn spl_sdl2_last_error_cstr() -> *const c_char;
    fn spl_sdl2_clipboard_get_cstr() -> *const c_char;
    fn spl_sdl2_clipboard_set_cstr(text: *const c_char) -> bool;
    fn spl_sdl2_get_display_name_cstr(index: i64) -> *const c_char;
    fn spl_sdl2_present_rgba_i64_view(handle: i64, pixels: *const i64, count: i64, width: i64, height: i64) -> bool;
}

fn owned_text(value: RuntimeValue) -> Option<CString> {
    // heap_type checks the owner registry before inspecting the header.
    if value.heap_type() != Some(HeapObjectType::String) {
        return None;
    }
    let length = rt_string_len(value);
    let data = rt_string_data(value);
    if length < 0 || (length != 0 && data.is_null()) {
        return None;
    }
    let bytes = if length == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(data, usize::try_from(length).ok()?) }
    };
    // Preserve the established C-string prefix at an embedded NUL. There is
    // no fixed-size buffer or truncation of a non-NUL-terminated owner string.
    let prefix = bytes.split(|byte| *byte == 0).next()?;
    CString::new(prefix).ok()
}

fn owned_pixels(value: RuntimeValue, count: usize) -> Option<Vec<i64>> {
    if value.heap_type() != Some(HeapObjectType::Array) {
        return None;
    }
    let array = unsafe { &*(value.as_heap_ptr() as *const RuntimeArray) };
    if array.is_byte_packed()
        || array.is_u64_packed()
        || array.len > array.capacity
        || count as u64 > array.len
        || (count != 0 && array.data.is_null())
        || count > isize::MAX as usize / std::mem::size_of::<RuntimeValue>()
    {
        return None;
    }
    let mut pixels = Vec::new();
    pixels.try_reserve_exact(count).ok()?;
    for index in 0..count {
        let pixel = unsafe { *array.data.add(index) };
        // [i64] pixels are signed values. Do not reinterpret tagged words,
        // unsigned packed arrays, or another registered heap object's header.
        pixels.push(if pixel.is_int() {
            pixel.as_int()
        } else {
            pixel.as_heap_i64()?
        });
    }
    Some(pixels)
}

unsafe fn owned_c_text(data: *const c_char) -> RuntimeValue {
    if data.is_null() {
        return rt_string_new(std::ptr::null(), 0);
    }
    let bytes = CStr::from_ptr(data).to_bytes();
    rt_string_new(bytes.as_ptr(), bytes.len() as u64)
}

#[no_mangle]
pub extern "C" fn rt_sdl2_create_window(title: RuntimeValue, width: i64, height: i64) -> i64 {
    let Some(title) = owned_text(title) else { return 0 };
    unsafe { spl_sdl2_create_window_cstr(title.as_ptr(), width, height) }
}

#[no_mangle]
pub extern "C" fn rt_sdl_create_window(title: RuntimeValue, width: i64, height: i64) -> i64 {
    rt_sdl2_create_window(title, width, height)
}

#[no_mangle]
pub extern "C" fn rt_sdl2_set_window_title(handle: i64, title: RuntimeValue) -> bool {
    let Some(title) = owned_text(title) else { return false };
    unsafe { spl_sdl2_set_window_title_cstr(handle, title.as_ptr()) }
}

#[no_mangle]
pub extern "C" fn rt_sdl_set_window_title(handle: i64, title: RuntimeValue) {
    rt_sdl2_set_window_title(handle, title);
}

#[no_mangle]
pub extern "C" fn rt_sdl2_present_rgba(handle: i64, pixels: RuntimeValue, width: i64, height: i64) -> bool {
    if width <= 0 || height <= 0 || width > i32::MAX as i64 / 4 || height > i32::MAX as i64 {
        return false;
    }
    let Some(count) = width.checked_mul(height).and_then(|count| usize::try_from(count).ok()) else {
        return false;
    };
    let Some(pixels) = owned_pixels(pixels, count) else {
        return false;
    };
    unsafe { spl_sdl2_present_rgba_i64_view(handle, pixels.as_ptr(), count as i64, width, height) }
}

#[no_mangle]
pub extern "C" fn rt_sdl_present_rgba(handle: i64, pixels: RuntimeValue, width: i64, height: i64) -> bool {
    rt_sdl2_present_rgba(handle, pixels, width, height)
}

#[no_mangle]
pub extern "C" fn rt_sdl2_event_text() -> RuntimeValue {
    unsafe { owned_c_text(spl_sdl2_event_text_cstr()) }
}

#[no_mangle]
pub extern "C" fn rt_sdl_event_text() -> RuntimeValue {
    rt_sdl2_event_text()
}

#[no_mangle]
pub extern "C" fn rt_sdl2_last_error() -> RuntimeValue {
    unsafe { owned_c_text(spl_sdl2_last_error_cstr()) }
}

#[no_mangle]
pub extern "C" fn rt_sdl2_clipboard_get() -> RuntimeValue {
    unsafe { owned_c_text(spl_sdl2_clipboard_get_cstr()) }
}

#[no_mangle]
pub extern "C" fn rt_sdl2_clipboard_set(text: RuntimeValue) -> bool {
    let Some(text) = owned_text(text) else { return false };
    unsafe { spl_sdl2_clipboard_set_cstr(text.as_ptr()) }
}

#[no_mangle]
pub extern "C" fn rt_sdl2_get_display_name(index: i64) -> RuntimeValue {
    unsafe { owned_c_text(spl_sdl2_get_display_name_cstr(index)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{rt_array_new, rt_array_new_with_cap_u64, rt_array_push};

    #[test]
    fn sdl_owner_pixel_values_are_unboxed_and_wrong_kinds_rejected() {
        let array = rt_array_new(3);
        for pixel in [0x12345678, 0xfedcba98, -1] {
            rt_array_push(array, RuntimeValue::from_int(pixel));
        }
        assert_eq!(owned_pixels(array, 3), Some(vec![0x12345678, 0xfedcba98, -1]));
        assert!(owned_pixels(array, 4).is_none());
        assert!(owned_pixels(rt_array_new_with_cap_u64(1), 0).is_none());
        assert!(owned_pixels(RuntimeValue::from_raw(0x12345679), 1).is_none());
        let text = rt_string_new(b"wrong kind".as_ptr(), 10);
        assert!(owned_pixels(text, 0).is_none());
        rt_array_push(array, RuntimeValue::from_bool(true));
        assert!(owned_pixels(array, 4).is_none());
    }

    #[test]
    fn sdl_owner_text_is_bounded_with_c_prefix_and_no_size_truncation() {
        let bytes = "窗口 α\0tail".as_bytes();
        let text = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
        assert_eq!(owned_text(text).unwrap().to_bytes(), "窗口 α".as_bytes());
        let bytes = vec![b'x'; 10000];
        assert_eq!(
            owned_text(rt_string_new(bytes.as_ptr(), bytes.len() as u64))
                .unwrap()
                .to_bytes()
                .len(),
            10000
        );
        assert!(owned_text(RuntimeValue::from_raw(0x12345679)).is_none());
        assert!(owned_text(rt_array_new(0)).is_none());
    }
}
