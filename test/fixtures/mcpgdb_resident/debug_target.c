#include <string.h>
#ifdef _WIN32
#include <windows.h>
#define tick() Sleep(1)
#else
#include <unistd.h>
#define tick() usleep(1000)
#endif
volatile int shared_value = 7;
volatile int keep_running = 1;
#if defined(__GNUC__)
__attribute__((noinline))
#endif
int debug_target(int input) {
    int local = input + 1;
    local += shared_value;
    shared_value = local;
    return local;
}
int main(int argc, char** argv) {
    if (argc > 1 && !strcmp(argv[1], "--loop")) {
        while (keep_running) { tick(); }
    }
    int result = debug_target(34);
    return result == 42 ? 0 : 1;
}
