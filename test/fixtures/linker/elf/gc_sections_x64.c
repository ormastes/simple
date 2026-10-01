long live_data = 2;
long dead_data = 99;
volatile long live_sink;
extern long missing_dead_dependency;

__attribute__((noinline)) long live_function(void) {
    return live_data;
}

__attribute__((noinline)) long dead_function(void) {
    return dead_data;
}

__attribute__((noinline)) long dead_undefined_function(void) {
    return missing_dead_dependency;
}

void _start(void) {
    live_sink = live_function();
}
