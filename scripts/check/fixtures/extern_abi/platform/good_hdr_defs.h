/* FIXTURE — not compiled. POSITIVE CONTROL for HEADER coverage.
   rt_dir_create and rt_dir_remove_all are really defined in
   src/runtime/platform/unix_common.h and platform/platform_win.h and were
   invisible to the depth-1 *.c scan (gap 1 in the family bug doc). This
   fixture proves a definition sitting in a nested HEADER is seen: it AGREES
   with good_spec.rs, so it must be extracted AND produce no mismatch. */
int rt_selftest_hdr(const uint8_t* path_ptr, uint64_t path_len) {
    return path_ptr != 0 && path_len > 0;
}
/* A pure DECLARATION must NOT be mistaken for a definition. */
const char* rt_selftest_hdr_decl_only(const char* path);
