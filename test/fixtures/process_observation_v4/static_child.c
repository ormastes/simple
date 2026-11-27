#include <unistd.h>

int main(void) {
    static const char output[] = "native-v4\n";
    if (write(STDOUT_FILENO, output, sizeof(output) - 1) !=
        (ssize_t)(sizeof(output) - 1)) {
        return 91;
    }
    return 23;
}
