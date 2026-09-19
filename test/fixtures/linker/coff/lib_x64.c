/* COFF linker fixture: library object providing base + add_val. */
int base = 2;
int scratch;

int add_val(int x) {
    scratch = x;
    return x + base;
}
