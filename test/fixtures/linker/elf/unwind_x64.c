__attribute__((noinline)) long unwind_add(long value) {
    return value + 3;
}

void _start(void) {
    (void)unwind_add(39);
}
