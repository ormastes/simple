//! Contract checking — implementation in src/runtime/runtime_contracts.c.

mod c_sffi {
    extern "C" {
        pub(super) fn simple_contract_check(condition: i64, kind: i64, func_name_ptr: *const u8, func_name_len: i64);
        pub(super) fn simple_contract_check_msg(
            condition: i64,
            kind: i64,
            func_name_ptr: *const u8,
            func_name_len: i64,
            message_ptr: *const u8,
            message_len: i64,
        );
    }
}

#[inline(always)]
pub unsafe fn simple_contract_check(condition: i64, kind: i64, func_name_ptr: *const u8, func_name_len: i64) {
    c_sffi::simple_contract_check(condition, kind, func_name_ptr, func_name_len)
}

#[inline(always)]
pub unsafe fn simple_contract_check_msg(
    condition: i64,
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
    message_ptr: *const u8,
    message_len: i64,
) {
    c_sffi::simple_contract_check_msg(condition, kind, func_name_ptr, func_name_len, message_ptr, message_len)
}
