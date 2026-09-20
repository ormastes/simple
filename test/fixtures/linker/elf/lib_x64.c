/* Object B (x86_64 twin): .text add_val, .rodata msg, .data base, .bss scratch. */
const char msg[] = "hi\n";
long base = 2;
long scratch;

long add_val(long x) {
    scratch = x;
    return scratch + base;
}
