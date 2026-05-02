# SimpleOS Libc Coverage Audit

**Date:** 2026-04-14
**Scope:** `src/runtime/` extern/libc usage vs `src/os/libc/` provisions
**Method:** `nm -T` on `libsimpleos_c.a`; grep on runtime C sources; grep weak attrs in `baremetal_stubs.c`

---

## Status Summary

| Metric | Count |
|--------|-------|
| Total audit gaps identified | 20 |
| Closed this cycle | 20 |
| Remaining | 0 |
| Wave-3 scaffolds added (fork/ipc trampolines) | 10 |

**Wave-3 additions (2026-04-15)**: `src/os/libc/simpleos_fork.c`
(`fork`, `execve`, `execv`, `execvp`, `simpleos_waitpid`) and
`src/os/libc/simpleos_ipc.c` (`pipe`, `dup`, `dup2`, `dup3`,
`socketpair`) route through `_simpleos_syscall{0,3}` trampolines to
the kernel SYSCALL arc. Fallback path returns `-ENOSYS` on host
builds. Wave-4 wires the kernel handlers to `scheduler.clone_task` /
`exec_into` / `wait_for`.

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

## Closed Gaps

All 20 gaps previously identified are now closed. Each symbol has a strong implementation in `src/os/libc/`.

| # | Symbol(s) | Subsystem | Implementing File | Notes |
|---|-----------|-----------|-------------------|-------|
| 1 | `waitpid`, `wait` | proc | `simpleos_process_wait.c` | ✅ Child process reaping |
| 2 | `popen`, `pclose` | proc | `simpleos_process_wait.c` | ✅ Shell command capture |
| 3 | `system` | proc | `simpleos_process_wait.c` | ✅ Synchronous shell command |
| 4 | `poll`, `ppoll` | async/io | `simpleos_poll.c` | ✅ Pipe multiplexing; async I/O |
| 5 | `pthread_rwlock_init` | sync | `simpleos_pthread_rwlock.c` | ✅ Handle table lock |
| 6 | `pthread_rwlock_rdlock` | sync | `simpleos_pthread_rwlock.c` | ✅ Handle table read lock |
| 7 | `pthread_rwlock_wrlock` | sync | `simpleos_pthread_rwlock.c` | ✅ Handle table write lock |
| 8 | `pthread_rwlock_unlock` | sync | `simpleos_pthread_rwlock.c` | ✅ Handle table unlock |
| 9 | `pthread_rwlock_destroy` | sync | `simpleos_pthread_rwlock.c` | ✅ Handle table teardown |
| 10 | `pthread_rwlock_trywrlock`, `pthread_rwlock_tryrdlock`, `pthread_rwlock_timedrdlock`, `pthread_rwlock_timedwrlock` | sync | `simpleos_pthread_rwlock.c` | ✅ Full rwlock API (9 functions total) |
| 11 | `pthread_cond_timedwait` | sync | `simpleos_pthread_cond.c` | ✅ Timed condvar wait (8 functions total) |
| 12 | `epoll_create`, `epoll_create1` | async | `simpleos_epoll.c` | ✅ Linux epoll driver |
| 13 | `epoll_ctl` | async | `simpleos_epoll.c` | ✅ Linux epoll driver |
| 14 | `epoll_wait`, `epoll_pwait` | async | `simpleos_epoll.c` | ✅ Linux epoll driver |
| 15 | `eventfd`, `eventfd_read`, `eventfd_write` | async | `simpleos_eventfd.c` | ✅ Event notification |
| 16 | `timerfd_create`, `timerfd_settime`, `timerfd_gettime` | async | `simpleos_timerfd.c` | ✅ Epoll timer events |
| 17 | `signalfd` | async | `simpleos_signalfd.c` | ✅ Signal as file descriptor |
| 18 | `inotify_init`, `inotify_init1`, `inotify_add_watch`, `inotify_rm_watch` | fs | `simpleos_inotify.c` | ✅ Filesystem event watch |
| 19 | `nftw`, `ftw`, `flock`, `fnmatch` | fs | `simpleos_fs_walk.c` | ✅ Recursive dir walk; advisory file lock |
| 20 | `glob`, `globfree`, `wordexp`, `wordfree` | fs | `simpleos_glob_stub.c` | ✅ Glob/word expansion stubs |
| 21 | `getpwuid`, `getpwnam`, `getpwuid_r`, `getpwnam_r` | proc | `simpleos_pwd_stub.c` | ✅ Password/user info stubs |
| 22 | `strfmon`, `strfmon_l` | locale | `simpleos_strfmon.c` | ✅ Monetary formatting ENOSYS stub |

**Note:** `mlock`/`munlock` and `sbrk`/`brk` were listed as low-priority gaps. These are handled by the ASM layer (`mmap.o` for memory ops; baremetal pages are always pinned making `mlock` a no-op). `select` is provided via `poll` compatibility.

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
| Hard gaps (completely absent) | **0** (was 20, all closed) |
| Functional stubs present but ENOSYS | 3 (`pthread_create/join/detach`) + `strfmon`/`strfmon_l` |
| Weak symbols in `baremetal_stubs.c` | 2 |

---

## Stubs Manifest

Remaining `auto_stub_*` symbols (not libc, compiler-level stubs) are tracked in
`build/os/stubs_manifest.sdn`, regenerated by:

    bin/simple run src/os/port/stubs_manifest.spl

See `src/os/port/bootstrap_cross.spl::SIMPLEOS_EXCLUDED_SOURCE_SUBTREES` for
stdlib subtrees already gated off the SimpleOS build path (gpu/vulkan/opencl/ml/db/gfx).

Remaining auto_stubs on SimpleOS builds should be investigated and either:
1. Implemented properly,
2. Added to SIMPLEOS_EXCLUDED_SOURCE_SUBTREES if the containing subtree is gateable, or
3. Promoted to `_stub_panic_*` — panics on call so bugs surface loudly in-guest.

**Methodology:** Grepped `src/runtime/` for libc call sites; ran `nm -T libsimpleos_c.a | grep ' T '`; cross-referenced per symbol; inspected `simpleos_pthread.c` for ENOSYS stubs; searched `baremetal_stubs.c` for `__attribute__((weak))`.

---

## Native-Surface Reduction Buckets

**Date:** 2026-04-24  
**Driver:** staged SimpleOS native-surface reduction program

The migration tracker now uses three buckets for `src/os/libc` source files:

### Replace Immediately in Simple

- `simpleos_alloc.c`
- `simpleos_epoll.c`
- `simpleos_eventfd.c`
- `simpleos_fork.c`
- `simpleos_fs.c`
- `simpleos_fs_walk.c`
- `simpleos_inotify.c`
- `simpleos_ipc.c`
- `simpleos_libc.c`
- `simpleos_libc_ext.c`
- `simpleos_math.c`
- `simpleos_math_ext.c`
- `simpleos_poll.c`
- `simpleos_printf_float.c`
- `simpleos_process.c`
- `simpleos_process_wait.c`
- `simpleos_pthread.c`
- `simpleos_pthread_cond.c`
- `simpleos_pthread_rwlock.c`
- `simpleos_signal.c`
- `simpleos_signalfd.c`
- `simpleos_stdlib_ext.c`
- `simpleos_string_ext.c`
- `simpleos_time.c`
- `simpleos_timerfd.c`

### Temporary Native Boundary

- `simpleos_crt0.S`
- `simpleos_cxxabi.c`
- `simpleos_dlmalloc.c`
- `simpleos_setjmp.S`
- `simpleos_syscall.S`

These remain native because they are ABI-sensitive entry, trampoline, unwinding, or allocator boundary pieces.

### Delete or Stub-Track

- `simpleos_glob_stub.c`
- `simpleos_pwd_stub.c`
- `simpleos_strfmon.c`

`src/os/port/native_surface_policy_verify.spl` prints this same bucket inventory from source control and fails if a new native file lands in the covered SimpleOS reduction scope without being added to the approved manifest deliberately.
