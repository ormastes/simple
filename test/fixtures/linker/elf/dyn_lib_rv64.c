/* riscv64 twin of lib_x64.c: .text add_val, .rodata msg, .data base, .bss scratch. */
const char msg[] = "hi\n";
int base = 2;
int scratch;

int add_val(int x) {
    scratch = x;
    return scratch + base;
}
