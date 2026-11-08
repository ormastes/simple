/* Compile -g3 -gdwarf-4 -fdebug-macro -O0. This is an owned debugger fixture. */
volatile int side_effects = 0;
__attribute__((used, noinline)) int counted_call(void) {
    ++side_effects;
    return 23;
}
#define counter counted_call()
#define assigned (side_effects = 41)
/* These unused replacement lists are debugger expressions, not C execution.
 * The register control is specific to the admitted x86_64 GNU test target. */
#define assigned_register ($rax = 42)
#define assigned_convenience ($mcp_fixture_only = 99)
__attribute__((used, noinline)) int inspection_stop(void) {
    volatile int ordinary = 17;
    return ordinary;
}
int main(void) {
    inspection_stop();
    return side_effects;
}
