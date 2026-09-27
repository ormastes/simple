int shared_block[12] __attribute__((aligned(32)));

void _start(void) {
    shared_block[3] = 7;
}
