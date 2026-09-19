/* --gc-sections fixture (lane C1), built with -ffunction-sections
   -fdata-sections so every function and datum is its own input section.

   Live from _start:  .text.gc_start -> .text.gc_add -> .text.gc_leaf,
                      .rodata.gc_msg, .data.gc_base, .bss.gc_scratch
   Dead:              .text.gc_dead (which itself calls .text.gc_dead_leaf
                      and reads .rodata.gc_dead_msg / .data.gc_dead_base),
                      .text.gc_dead_leaf, .rodata.gc_dead_msg,
                      .data.gc_dead_base, .bss.gc_dead_scratch

   gc_dead is never referenced, so a mark-from-roots pass must drop it and
   everything only it reaches, while keeping the live chain. Writes "gc\n"
   and exits 40 + 2 = 42. */

const char gc_msg[] = "gc\n";
const char gc_dead_msg[] = "dead\n";
long gc_base = 2;
long gc_dead_base = 7;
long gc_scratch;
long gc_dead_scratch;
long gc_ctor_ran;

static long sys3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}

__attribute__((noinline)) long gc_leaf(long x) { return x + gc_base; }

__attribute__((noinline)) long gc_add(long x) {
    gc_scratch = gc_leaf(x);
    return gc_scratch;
}

__attribute__((noinline)) long gc_dead_leaf(long x) { return x + gc_dead_base; }

__attribute__((noinline)) long gc_dead(long x) {
    gc_dead_scratch = gc_dead_leaf(x) + (long)gc_dead_msg;
    return gc_dead_scratch;
}

__attribute__((retain, used, noinline)) long gc_retained(long x) { return x + 5; }

/* Reached only through .init_array (an SHT_INIT_ARRAY root), and .init is a
   root by name -- both must survive --gc-sections. */
__attribute__((noinline)) void gc_ctor(void) { gc_ctor_ran = 1; }
__asm__(".section .init_array,\"aw\",%init_array\n.p2align 3\n.quad gc_ctor\n.text\n");

__attribute__((section(".init"), noinline)) long gc_in_init(long x) { return x + 9; }

void _start(void) {
    sys3(64, 1, (long)gc_msg, 3);
    sys3(93, gc_add(40), 0, 0);
    for (;;) {}
}
