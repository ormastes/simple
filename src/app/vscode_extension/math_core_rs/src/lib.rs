#![deny(unsafe_op_in_unsafe_fn)]

mod abi;
mod parser;
mod render;

pub use abi::{rt_alloc, rt_free};

#[no_mangle]
pub extern "C" fn render_math_core_json(
    input_ptr: *const u8,
    input_len: usize,
    out_len_ptr: *mut usize,
) -> *mut u8 {
    render::render_math_core_json(input_ptr, input_len, out_len_ptr)
}
