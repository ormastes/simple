/* RELRO fixture (lane C1): one input section for each PT_GNU_RELRO member
   ld.lld places in a dynamic PIE -- .init_array (constructor), .fini_array
   (destructor), .data.rel.ro (a const table of code pointers) -- plus .got
   (puts/exit via the PLT, main via Scrt1) and .dynamic. Prints "relro ok",
   exits 40 + 2 = 42. */
int puts(const char *s);
void exit(int code);

int ctor_ran;
static volatile int fini_seen;
volatile int idx;

__attribute__((constructor)) void init_hook(void) { ctor_ran = 40 + idx; }
__attribute__((destructor)) void fini_hook(void) { fini_seen = 1; }

int two(void) { return 2; }
int (*const table[])(void) = { two };

int main(void) {
    puts("relro ok");
    exit(ctor_ran + table[idx]());
}
