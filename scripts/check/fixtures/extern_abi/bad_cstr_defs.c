/* FIXTURE — not compiled. PLANTED DEFECT, class 1:
   the compiler declares (ptr, len) = 2 words, this copy takes a single
   const char*. This is the rt_file_is_char_device shape (81fca37cdd4). */
int rt_selftest_cstr(const char* path) {
    return path != 0;
}
