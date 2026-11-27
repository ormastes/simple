/* Compile -g3 -gdwarf-4 -O0 -std=c++17; all debugger-call targets emitted. */
volatile int side_effects = 0;
struct Leaf { int field; };
struct Probe {
    Leaf leaf;
    int values[2];
    __attribute__((used, noinline)) int operator[](int index) {
        ++side_effects;
        return values[index];
    }
    __attribute__((used, noinline)) Leaf* operator->() {
        ++side_effects;
        return &leaf;
    }
    __attribute__((used, noinline)) int operator*() {
        ++side_effects;
        return leaf.field;
    }
};
Probe probe = {{31}, {11, 12}};
__attribute__((used, noinline)) int inspection_stop(void) {
    volatile int ordinary = probe.leaf.field;
    return ordinary;
}
int main() {
    inspection_stop();
    return side_effects;
}
