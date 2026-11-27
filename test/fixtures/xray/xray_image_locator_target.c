__attribute__((xray_always_instrument, noinline)) int locator_target(int x) { return x + 7; }
