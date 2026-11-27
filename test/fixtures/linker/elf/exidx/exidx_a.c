/* .ARM.exidx fixture: two functions in separate sections with unwind tables; b() is
 * placed before a() in link order to exercise SHF_LINK_ORDER sorting. */
int counter;
__attribute__((noinline)) int fa(int x) { counter += x; return counter * 3; }
__attribute__((noinline)) int fdead(int x) { return x - 1; }
