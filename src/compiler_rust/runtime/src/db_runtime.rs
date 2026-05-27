// Extern declarations for C runtime DB functions (runtime_db.c).
// These are detected by build.rs `runtime_defines_symbol` and registered
// in RUNTIME_SYMBOL_ENTRIES so the JIT can resolve their addresses.

unsafe extern "C" {
    pub fn rt_db_table_create(name: *const u8, num_cols: i64, pk_col: i64) -> i64;
    pub fn rt_db_table_destroy(handle: i64);
    pub fn rt_db_put(table: i64, pk_text: *const u8, num_values: i64) -> i64;
    pub fn rt_db_put_value_int(table: i64, row: i64, col: i64, value: i64);
    pub fn rt_db_put_value_text(table: i64, row: i64, col: i64, value: *const u8);
    pub fn rt_db_get(table: i64, pk_text: *const u8) -> i64;
    pub fn rt_db_get_int(table: i64, row: i64, col: i64) -> i64;
    pub fn rt_db_get_text(table: i64, row: i64, col: i64) -> *const u8;
    pub fn rt_db_scan_range(table: i64, col: i64, low: i64, high: i64) -> i64;
    pub fn rt_db_scan_result(table: i64, result_idx: i64) -> i64;
    pub fn rt_db_delete(table: i64, pk_text: *const u8) -> i64;
    pub fn rt_db_row_count(table: i64) -> i64;
    pub fn rt_db_col_count(table: i64) -> i64;
    // Batched operations
    pub fn rt_db_put_row3(handle: i64, pk: *const u8, type_mask: i64, v0: i64, v1: i64, v2: i64) -> i64;
    pub fn rt_db_get_int_by_pk(handle: i64, pk: *const u8, col: i64, default_val: i64) -> i64;
    pub fn rt_db_update_int(handle: i64, pk: *const u8, col: i64, value: i64) -> i64;
    pub fn rt_db_update_text(handle: i64, pk: *const u8, col: i64, value: *const u8) -> i64;
}
