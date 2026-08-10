/* FIXTURE — not compiled. Definition that AGREES with good_spec.rs. */
int rt_selftest_ok_c(const uint8_t* p, uint64_t len) {
    return p != 0 && len > 0;
}
static int rt_selftest_ignored_static(int a) { return a; }
