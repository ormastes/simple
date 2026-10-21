#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>
int main(int argc, char **argv) {
  if (argc != 2) return 2;
  puts("PROBE_STARTED");
  fflush(stdout);
  int fd = open(argv[1], O_RDONLY | O_CLOEXEC);
  if (fd >= 0) {
    close(fd);
    puts("OPEN_STATUS=ALLOWED");
    return 0;
  }
  if (errno == EACCES || errno == EPERM) {
    puts("OPEN_STATUS=DENIED");
    return 0;
  }
  printf("OPEN_STATUS=OTHER errno=%d\n", errno);
  return 3;
}
