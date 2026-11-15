/* The SimpleOS sysroot cross-compile of the real runtime
 * (src/os/port/llvm/sysroot.shs) failed with undeclared ESTALE
 * (runtime_workspace_storage_v1.c) and O_NOFOLLOW
 * (runtime_file_lock_owned_v2.c). Values are the Linux ones, matching the
 * rest of these headers. SimpleOS has no symlinks (simpleos_fs.c lstat), so
 * libc open() strips O_NOFOLLOW before the syscall: vacuously honoured. */
#include "src/os/libc/include/errno.h"
#include "src/os/libc/include/fcntl.h"

_Static_assert(ESTALE == 116, "SimpleOS errno.h must define ESTALE (Linux value 116)");
_Static_assert(O_NOFOLLOW == 0x20000, "SimpleOS fcntl.h must define O_NOFOLLOW (Linux value)");
_Static_assert((O_NOFOLLOW & (O_WRONLY | O_RDWR | O_CREAT | O_EXCL | O_TRUNC | O_APPEND | O_NONBLOCK | O_CLOEXEC)) == 0, "O_NOFOLLOW must not alias another open flag");

int main(void) { return 0; }
