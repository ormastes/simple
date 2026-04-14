# SimpleOS Libc Coverage Audit

**Date:** 2026-04-14
**Scope:** `src/runtime/` extern/libc usage vs `src/os/libc/` provisions
**Method:** `nm -T` on `libsimpleos_c.a`; grep on runtime C sources; grep weak attrs in `baremetal_stubs.c`

---

## Runtime Expectations

Functions the Simple runtime calls from the OS-side libc (~85 symbols, grouped by subsystem).

| Subsystem | Functions | Primary Declaring Files |
|-----------|-----------|------------------------|
| **mem** | `malloc`, `calloc`, `realloc`, `free`, `mmap`, `munmap`, `mprotect`, `madvise`, `mlock`, `munlock`, `posix_memalign`, `sbrk`/`brk` | `runtime.c`, `runtime_thread.c`, `unix_common.h` |
| **string** | `mem{cpy,move,set,cmp}`, `str{len,cmp,ncmp,cpy,dup}`, `snprintf`, `vsnprintf`, `fprintf`, `printf`, `strtol`, `strtod` | `runtime.c`, `runtime_native.c` |
| **fs** | `open`, `close`, `read`, `write`, `lseek`, `fopen/fclose/fread/fwrite/fgets/fseek/ftell/fflush`, `stat`, `fstat`, `opendir/readdir/closedir`, `mkdir/rmdir/unlink/rename/remove`, `getcwd`, `chdir`, `access`, `fcntl`, `flock`, `nftw`, `popen`, `pclose`, `realpath`, `dup`, `dup2`, `pipe` | `runtime.c`, `runtime_native.c`, `runtime_fork.c`, `unix_common.h` |
| **proc** | `fork`, `execvp`, `execve`, `waitpid`, `kill`, `getpid`, `getppid`, `_exit`, `exit`, `getenv/setenv/unsetenv`, `signal`, `sigaction`, `sigprocmask`, `dlopen/dlsym/dlclose/dlerror` | `runtime.c`, `runtime_fork.c`, `unix_common.h` |
| **time** | `clock_gettime`, `gettimeofday`, `nanosleep`, `usleep`, `sleep` | `runtime_thread.c`, `runtime_fork.c`, `unix_common.h` |
| **sync** | `pthread_{create,join,detach,self}`, `pthread_mutex_{init,lock,trylock,unlock,destroy}`, `pthread_rwlock_{init,rdlock,wrlock,unlock,destroy}`, `pthread_cond_{init,wait,timedwait,signal,broadcast,destroy}`, `sysconf` | `runtime_thread.c` |
| **async** | `poll`, `select`, `epoll_create1`, `epoll_ctl`, `epoll_wait`, `timerfd_create` | `runtime_fork.c`, `async_driver.c`, `async_linux_epoll.c` |

---

## Libc Provided

All symbols exported by `src/os/libc/libsimpleos_c.a` (`nm -T`), ~175 total. Key source files:

| Source File | Key Provided Symbols |
|-------------|----------------------|
| `simpleos_libc.c` | `strlen/cpy/cmp/cat/chr/str/dup`, `mem{cpy,move,set,cmp}`, `read`, `write`, `open`, `close`, `{v,s,f}printf`, `exit`, `abort`, `getpid` |
| `simpleos_fs.c` | `stat`, `fstat`, `lstat`, `f{open,close,read,write,seek,tell,flush,eof,error,gets,getc}`, `opendir`, `readdir`, `closedir`, `mkdir`, `rmdir`, `unlink`, `rename`, `getcwd`, `chdir`, `dup`, `dup2`, `pipe`, `fcntl`, `access`, `lseek`, `ftruncate`, `perror`, `freopen` |
| `simpleos_process.c` | `getenv`, `setenv`, `unsetenv`, `fork`, `execve`, `execvp`, `getppid`, `get{u,g,eu,eg}id`, `system`, `sleep`, `usleep`, `sysconf` |
| `simpleos_pthread.c` | `pthread_create`(→ENOSYS), `pthread_{join,detach}`(→ENOSYS), `pthread_self`, `pthread_mutex_{init,lock,trylock,unlock,destroy}`, `pthread_cond_{init,wait,signal,broadcast,destroy}`, `pthread_{once,key_*,attr_*}` |
| `simpleos_time.c` | `clock_gettime`, `gettimeofday`, `nanosleep`, `time`, `gmtime`, `localtime`, `mktime`, `strftime` |
| `simpleos_signal.c` | `signal`, `sigaction`, `sig{empty,fill,add,del,ismember}set`, `sigprocmask`, `kill`, `raise` |
| `simpleos_alloc.c` | `posix_memalign`, `aligned_alloc`, `memalign`, `valloc` |
| `simpleos_dlmalloc.c` | `malloc`, `calloc`, `realloc`, `free` |
| `simpleos_math{,_ext}.c` | `fabs`, `sqrt`, `sin/cos/tan`, `atan2`, `exp/log/pow`, `ceil/floor/round`, `fmod`, `hypot`, `__fpclassify`, `__isnan`, `__isinf` |
| `simpleos_string_ext.c` | `strerror`, `strtok{,_r}`, `strndup`, `mem{chr,rchr}`, `str{casecmp,lcpy,lcat}` |
| `simpleos_stdlib_ext.c` | `strtol/ul/ll/ull`, `strtod/f`, `div/ldiv/lldiv`, `rand`, `srand` |
| `simpleos_libc_ext.c` | `realpath`, `putenv`, `gmtime_r`, `localtime_r`, `setlocale`, `wcslen/cmp`, `mbstowcs` |
| `simpleos_cxxabi.c` | `atexit`, `__cxa_{atexit,finalize,pure_virtual,guard_*}`, `__stack_chk_fail`, `__libc_init_array`, `_Exit`, `new`/`delete` ops |
| ASM objects | `mmap/mprotect/munmap/madvise` (mmap.o), `dlopen/sym/close/error` (dlfcn.o), `setjmp/longjmp` (setjmp.S), `_start` (crt0.S), `simpleos_syscall` (syscall.S), wchar/dirent/locale/spawn |

---

## Gap Matrix

Functions required by the runtime that are **absent** from `libsimpleos_c.a`.

| # | Missing Symbol | Subsystem | Used In | Notes |
|---|---------------|-----------|---------|-------|
| 1 | `poll` | async/io | `runtime_fork.c`, `async_driver.c`, `async_linux_epoll.c` | Pipe multiplexing; fork isolation; async I/O |
| 2 | `waitpid` | proc | `runtime.c`, `runtime_fork.c` | Child process reaping |
| 3 | `popen` | proc | `runtime.c` | Shell command capture (`spl_shell_run`) |
| 4 | `pclose` | proc | `runtime.c` | Paired with `popen` |
| 5 | `pthread_rwlock_init` | sync | `runtime_thread.c` | Handle table lock |
| 6 | `pthread_rwlock_rdlock` | sync | `runtime_thread.c` | Handle table read lock |
| 7 | `pthread_rwlock_wrlock` | sync | `runtime_thread.c` | Handle table write lock |
| 8 | `pthread_rwlock_unlock` | sync | `runtime_thread.c` | Handle table unlock |
| 9 | `pthread_rwlock_destroy` | sync | `runtime_thread.c` | Handle table teardown |
| 10 | `pthread_cond_timedwait` | sync | `runtime_thread.c` | Timed condvar wait |
| 11 | `epoll_create1` | async | `async_linux_epoll.c` | Linux epoll driver |
| 12 | `epoll_ctl` | async | `async_linux_epoll.c` | Linux epoll driver |
| 13 | `epoll_wait` | async | `async_linux_epoll.c` | Linux epoll driver |
| 14 | `timerfd_create` | async | `async_linux_epoll.c` | Epoll timer events |
| 15 | `flock` | fs | `unix_common.h` | Advisory file lock |
| 16 | `nftw` | fs | `unix_common.h` | Recursive directory walk (`rt_dir_remove_recursive`) |
| 17 | `mlock` | mem | `unix_common.h` | Pin pages in RAM |
| 18 | `munlock` | mem | `unix_common.h` | Unpin pages |
| 19 | `select` | async | `select_compat.spl` | POSIX select (legacy I/O compat) |
| 20 | `sbrk` / `brk` | mem | (allocator ABI) | dlmalloc fallback path |
| — | `pipe2` | fs | (linux-specific) | Non-blocking pipe; workaround: `pipe`+`fcntl` |
| — | `getpagesize` | mem | `unix_common.h` | Substitute: `sysconf(_SC_PAGESIZE)` available |

**Note:** `pthread_create`, `pthread_join`, `pthread_detach` are present but are strong ENOSYS stubs — they link but always return `ENOSYS` (single-threaded OS only).

---

## Priority Fix List

Top gaps sorted by estimated blocking impact (proc > sync > async > fs > mem):

| Priority | Symbol(s) | Impact |
|----------|-----------|--------|
| 1 | `waitpid` | **Critical** — `fork()` leaks zombies; blocks test isolation and process spawning |
| 2 | `poll` | **Critical** — `rt_fork_parent_wait()` deadlocks; kills test runner pipe capture |
| 3 | `popen` / `pclose` | **High** — `spl_shell_run()` is dead; build-system pipe capture broken |
| 4 | `pthread_rwlock_*` (5) | **High** — handle-table lock absent; data races on any concurrent handle use |
| 5 | `pthread_cond_timedwait` | **High** — timed condvar waits never time out silently |
| 6 | `nftw` | **Medium** — `rt_dir_remove_recursive()` cannot delete directories |
| 7 | `flock` | **Medium** — advisory file locking unavailable |
| 8 | `epoll_create1/ctl/wait` | **Medium** — Linux async I/O driver cannot initialize |
| 9 | `timerfd_create` | **Medium** — epoll timer events unimplemented |
| 10 | `select` | **Low-Medium** — legacy I/O compat layer non-functional |
| 11 | `mlock` / `munlock` | **Low** — baremetal pages always pinned anyway |
| 12 | `sbrk` / `brk` | **Low** — dlmalloc `mmap`-based path is primary and works |
| 13 | `getpagesize` | **Low** — `sysconf(_SC_PAGESIZE)` substitute available |
| 14 | `pipe2` | **Low** — `pipe()` + `fcntl(O_NONBLOCK)` workaround exists |

---

## Already-Stubbed-Weakly

Symbols in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` with `__attribute__((weak))`:

| Symbol | Line | Purpose |
|--------|------|---------|
| `kernel__arch__x86_64__interrupt__x86_dispatch_installed_syscall_abi` | 3431 | Weak syscall dispatch gate; falls back to `-ENOSYS` |
| `spl_start` | 5832 | Weak OS entry point; boot prints error if absent |

No standard libc symbols are declared weak in `baremetal_stubs.c`. All POSIX stubs in `libsimpleos_c.a` are **strong** symbols.

---

## Summary

| Metric | Count |
|--------|-------|
| Runtime-expected libc symbols examined | ~85 |
| Symbols provided by `libsimpleos_c.a` | ~175 |
| Hard gaps (completely absent) | **20** |
| Functional stubs present but ENOSYS | 3 (`pthread_create/join/detach`) |
| Weak symbols in `baremetal_stubs.c` | 2 |

**Methodology:** Grepped `src/runtime/` for libc call sites; ran `nm -T libsimpleos_c.a | grep ' T '`; cross-referenced per symbol; inspected `simpleos_pthread.c` for ENOSYS stubs; searched `baremetal_stubs.c` for `__attribute__((weak))`.
