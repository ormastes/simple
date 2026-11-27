#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
__attribute__((constructor)) static void injected(void) {
    const char *marker = getenv("SOSIX_INJECTION_MARKER");
    if (!marker) return;
    int fd = open(marker, O_CREAT | O_WRONLY | O_TRUNC, 0600);
    if (fd >= 0) { (void)write(fd, "injected", 8); close(fd); }
}
