#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
static volatile unsigned char simple_bootstrap_pad[1572864] __attribute__((section(".data")));
static int try_seed(const char *seed, int argc, char **argv) {
  if (!seed || seed[0] == '\0') return 127;
  if (argc > 0) argv[0] = (char *)seed;
  execv(seed, argv);
  return errno;
}
int main(int argc, char **argv) {
  const char *env_seed = getenv("SIMPLE_BOOTSTRAP_SEED");
  if (simple_bootstrap_pad[0] == 255) fprintf(stderr, "pad\n");
  int err = try_seed(env_seed, argc, argv);
  if (!env_seed || env_seed[0] == '\0') {
    err = try_seed("src/compiler_rust/target/bootstrap/simple", argc, argv);
    err = try_seed("target/bootstrap/simple", argc, argv);
    err = try_seed("../compiler_rust/target/bootstrap/simple", argc, argv);
  }
  errno = err;
  perror(env_seed && env_seed[0] ? env_seed : "simple bootstrap seed");
  return 127;
}
