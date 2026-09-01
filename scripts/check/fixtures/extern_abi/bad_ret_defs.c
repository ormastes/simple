/* FIXTURE — not compiled. PLANTED DEFECT, class 3 (RETURN type):
   the compiler declares the RESULT as &[I64] -- a RuntimeValue -- but this
   copy returns a raw `const char*`. The caller decodes a bare heap pointer as
   a tagged value, so a successful read comes back with no string tag and reads
   as len=0: indistinguishable from an empty file or a missing one. This is the
   rt_file_read_text shape. Parameter arity AGREES here on purpose, so this
   fixture is only detected by the RETURN-type comparison. */
const char* rt_selftest_ret(const uint8_t* path_ptr, uint64_t path_len) {
    return (const char*)(path_len ? path_ptr : 0);
}
