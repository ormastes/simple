/* Deliberately violates the static-off artifact contract. */
#include <dlfcn.h>

volatile int mcdc_probe_table[4];

int main(int argc, char **argv) {
    if (argc == 991) mcdc_probe_table[0]++;
    return dlopen(argv[0], RTLD_LAZY) == 0;
}
