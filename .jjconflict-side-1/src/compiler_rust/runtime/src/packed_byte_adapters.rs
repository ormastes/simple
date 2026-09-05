//! Fixed call-scoped adapters for C runtime consumers of packed bytes.

use crate::value::{byte_array_bytes, RuntimeValue};

unsafe extern "C" {
    fn rt_font_load_bytes(data_ptr: i64, data_len: i64) -> i64;
}

#[no_mangle]
pub extern "C" fn rt_font_load_array(data: RuntimeValue) -> i64 {
    let Some(bytes) = byte_array_bytes(data) else {
        return 0;
    };
    if bytes.is_empty() {
        return 0;
    }
    unsafe { rt_font_load_bytes(bytes.as_ptr() as i64, bytes.len() as i64) }
}
