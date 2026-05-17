//! Ctype compatibility shims — implementations in src/runtime/runtime_ctype.c.

mod c_ffi {
    extern "C" {
        pub(super) fn __is_alnum(ch: i32) -> i32;
        pub(super) fn __is_alpha(ch: i32) -> i32;
        pub(super) fn __is_digit(ch: i32) -> i32;
        pub(super) fn __is_xdigit(ch: i32) -> i32;
        pub(super) fn __is_space(ch: i32) -> i32;
        pub(super) fn __is_lower(ch: i32) -> i32;
        pub(super) fn __is_upper(ch: i32) -> i32;
    }
}
