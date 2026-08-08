# Per Target Build Specification

> _Scaffolding checks for the multi-target cross-build + compiler-rt stage._

<!-- sdn-diagram:id=per_target_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=per_target_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

per_target_build_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=per_target_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 59 | 59 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per Target Build Specification

## Scenarios

### SimpleOS LLVM per-target build (A4/A5)
_Scaffolding checks for the multi-target cross-build + compiler-rt stage._

#### declares CROSS_SUPPORTED_TARGETS

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("val CROSS_SUPPORTED_TARGETS"))
```

</details>

#### CROSS_SUPPORTED_TARGETS lists all five SimpleOS triples

- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("x86_64-unknown-simpleos"))
check(src.contains("aarch64-unknown-simpleos"))
check(src.contains("armv7-unknown-simpleos"))
check(src.contains("riscv64gc-unknown-simpleos"))
check(src.contains("riscv32imac-unknown-simpleos"))
```

</details>

#### honours SIMPLE_TARGET env override

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("SIMPLE_TARGET"))
check(src.contains("cross_selected_targets"))
```

</details>

#### cross_build_all iterates CROSS_SUPPORTED_TARGETS

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("fn cross_build_all"))
check(src.contains("cross_build_stage_for_target"))
```

</details>

#### exports build_compiler_rt(triple)

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("fn build_compiler_rt(triple: text)"))
```

</details>

#### exports build_compiler_rt_for_target

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("fn build_compiler_rt_for_target"))
```

</details>

#### registers compiler-rt subcommand in cross_build_main

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("\"compiler-rt\""))
check(src.contains("subcommand"))
```

</details>

#### exposes --print-plan CLI flag

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("--print-plan"))
```

</details>

#### stages builtins into clang resource dir

- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
val shs = build_shs_src()
check(src.contains("lib/clang/"))
check(src.contains("CLANG_RESOURCE_VERSION"))
check(src.contains("CLANG_RESOURCE_VERSION: text = \"20\""))
check(shs.contains("CLANG_RES_VERSION="))
check(shs.contains(":-20"))
```

</details>

#### gates compiler-rt behind -simpleos triples

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("ends_with(\"-simpleos\")"))
```

</details>

#### per-target build dir is cross-<triple>

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("cross-"))
```

</details>

#### compiler-rt build dir is compiler-rt-<triple>

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("compiler-rt-"))
```

</details>

#### build.shs threads SIMPLEOS_TARGET_TRIPLE

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("SIMPLEOS_TARGET_TRIPLE"))
check(src.contains("SIMPLE_TARGET"))
```

</details>

#### build.spl uses std.process run for staged shell calls

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
check(src.contains("process.run(\"sh\", [\"src/os/port/llvm/build.shs\", stage])"))
```

</details>

#### build.shs uses per-triple CROSS_DIR / RT_DIR

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("CROSS_DIR="))
check(src.contains("RT_DIR="))
```

</details>

#### build.shs still dispatches compiler-rt subcommand

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("compiler-rt)"))
check(src.contains("stage3_compiler_rt"))
```

</details>

#### build.shs lets compiler-rt derive the default target triple

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("-UCOMPILER_RT_DEFAULT_TARGET_TRIPLE"))
check(!src.contains("-DCOMPILER_RT_DEFAULT_TARGET_TRIPLE"))
check(src.contains("-DCMAKE_C_COMPILER_TARGET=\"$TRIPLE\""))
```

</details>

#### compiler-rt preload does not inject an empty sysroot flag

- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build = build_shs_src()
val cache = rt_cmake_src()
check(build.contains("-UCMAKE_EXE_LINKER_FLAGS"))
check(build.contains("-UCMAKE_C_FLAGS"))
check(build.contains("-UCMAKE_CXX_FLAGS"))
check(build.contains("-UCMAKE_ASM_FLAGS"))
check(!cache.contains("set(CMAKE_C_FLAGS"))
check(!cache.contains("set(CMAKE_CXX_FLAGS"))
check(!cache.contains("set(CMAKE_ASM_FLAGS"))
```

</details>

#### build.shs maps armv7 to LLVM ARM

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("armv7-*)"))
check(src.contains("LLVM_ARCH=\"ARM\""))
```

</details>

#### build.shs preflights SimpleOS C++ standard headers

- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("check_cxx_runtime_headers"))
check(src.contains("#include <iosfwd>"))
check(src.contains("SimpleOS C++ standard headers are not available"))
check(src.contains("sys/utsname.h"))
```

</details>

#### build.shs rebuilds sysroot when target marker mismatches

- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("ensure_target_sysroot"))
check(src.contains("sysroot_target_matches"))
check(src.contains("target-triple.txt"))
check(src.contains("|| ! sysroot_target_matches"))
check(src.contains("Direct compiler-rt invocations also need the target-matched shared sysroot"))
```

</details>

#### sysroot.shs stages libc++ headers

- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sysroot_shs_src()
check(src.contains("libcxx/include"))
check(src.contains("build_libcxx_runtime"))
check(src.contains("build_libc_runtime"))
check(src.contains("libc-$TRIPLE"))
check(src.contains("aarch64-*"))
check(src.contains("simpleos_crt0_aarch64.S"))
check(src.contains("simpleos_syscall_aarch64.S"))
check(src.contains("simpleos_setjmp_aarch64.S"))
check(src.contains("install_compiler_builtins_seed"))
check(src.contains("libclang_rt.builtins-aarch64.a"))
check(src.contains("libc++.a"))
check(src.contains("include/c++/v1"))
check(src.contains("__config_site"))
check(src.contains("__assertion_handler"))
check(src.contains("_LIBCPP_HAS_THREADS 1"))
check(src.contains("_LIBCPP_HAS_CLOCK_GETTIME 1"))
check(src.contains("_LIBCPP_HAS_THREAD_API_PTHREAD 1"))
check(src.contains("_LIBCPP_HAS_RANDOM_DEVICE 1"))
check(src.contains("_LIBCPP_HAS_LOCALIZATION 0"))
check(src.contains("_LIBCPP_HAS_WIDE_CHARACTERS 1"))
check(src.contains("_LIBCPP_PROVIDES_DEFAULT_RUNE_TABLE 1"))
check(src.contains("_LIBCPP_PSTL_BACKEND_SERIAL"))
```

</details>

#### LLVM toolchain searches libc++ before C headers

- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = llvm_toolchain_src()
check(src.contains("include/c++/v1"))
check(src.contains("CMAKE_C_COMPILER_TARGET"))
check(src.contains("CMAKE_CXX_COMPILER_TARGET"))
check(src.contains("CMAKE_ASM_COMPILER_TARGET"))
check(src.contains("--target="))
check(src.contains("SIMPLEOS_TARGET_TRIPLE}"))
check(src.contains("-isystem"))
check(src.contains("SIMPLEOS_SYSROOT}/include"))
check(src.contains("CMAKE_C_FLAGS"))
check(src.contains("CMAKE_CXX_FLAGS"))
check(src.contains("SIMPLEOS_CXX_LINK_RUNTIME"))
check(src.contains("SIMPLEOS_LLD_EMULATION"))
check(src.contains("SIMPLEOS_COMPILER_RT_ARCH"))
check(src.contains("SIMPLEOS_BUILTINS_ARCHIVE"))
check(src.contains("-Wl,-m,"))
check(src.contains("SIMPLEOS_LLD_EMULATION}"))
check(src.contains("aarch64elf"))
check(src.contains("CMAKE_CXX_STANDARD_LIBRARIES"))
check(src.contains("crt0.o"))
check(src.contains("__bss_end=_end"))
check(src.contains("-no-pie"))
check(src.contains("--export-dynamic"))
check(src.contains("-lc++"))
check(src.contains("-lsimpleos_c"))
check(src.contains("-lm"))
```

</details>

#### LLVM toolchain advertises Unix-style support for SimpleOS

- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = llvm_toolchain_src()
check(src.contains("set(CMAKE_SYSTEM_NAME Linux)"))
check(src.contains("target triple and sysroot as SimpleOS"))
check(src.contains("Unix-style Support library"))
check(src.contains("HAVE_GETPAGESIZE 1"))
check(src.contains("HAVE_SYSCONF 1"))
check(src.contains("HAVE_GETRUSAGE 1"))
```

</details>

#### SimpleOS libc has C++ port support headers

- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(regular_file_exists(ASSERT_H))
check(regular_file_exists(CTYPE_H))
check(regular_file_exists(ENDIAN_H))
check(regular_file_exists(INTTYPES_H))
check(regular_file_exists(LIMITS_H))
check(regular_file_exists(LOCALE_H))
check(regular_file_exists(MBSTATE_H))
check(regular_file_exists(STDLIB_H))
check(regular_file_exists(STRING_H))
check(regular_file_exists(SYSEXITS_H))
check(regular_file_exists(TIME_H))
check(regular_file_exists(SCHED_H))
check(regular_file_exists(SYS_RESOURCE_H))
check(regular_file_exists(SYS_TIME_H))
check(regular_file_exists(PWD_H))
check(regular_file_exists(SYS_SOCKET_H))
check(regular_file_exists(SYS_UN_H))
check(regular_file_exists(SYS_FILE_H))
check(regular_file_exists(SYS_STATVFS_H))
check(regular_file_exists(SYS_VFS_H))
check(regular_file_exists(SYS_UTSNAME_H))
check(regular_file_exists(WCTYPE_H))
```

</details>

#### SimpleOS assert header exposes C11 static_assert

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [ASSERT_H]).stdout
check(src.contains("#define static_assert _Static_assert"))
```

</details>

#### SimpleOS limits header follows target char signedness

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [LIMITS_H]).stdout
check(src.contains("__CHAR_UNSIGNED__"))
check(src.contains("#define CHAR_MIN   0"))
check(src.contains("#define CHAR_MAX   UCHAR_MAX"))
```

</details>

#### SimpleOS libc exposes libc++ C-locale fallback declarations

- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctype = process.run("cat", [CTYPE_H]).stdout
val locale = process.run("cat", [LOCALE_H]).stdout
val stdlib = process.run("cat", [STDLIB_H]).stdout
val string = process.run("cat", [STRING_H]).stdout
val time = process.run("cat", [TIME_H]).stdout
val wchar = process.run("cat", [WCHAR_H]).stdout
val wctype = process.run("cat", [WCTYPE_H]).stdout
check(ctype.contains("isascii"))
check(ctype.contains("isprint_l"))
check(locale.contains("LC_COLLATE_MASK"))
check(locale.contains("newlocale"))
check(stdlib.contains("strtod_l"))
check(stdlib.contains("mbtowc"))
check(string.contains("strcoll_l"))
check(time.contains("strftime_l"))
check(wchar.contains("mbsrtowcs"))
check(wchar.contains("wcsxfrm_l"))
check(wctype.contains("iswspace_l"))
check(wctype.contains("towlower_l"))
```

</details>

#### SimpleOS wchar header exposes libc++ wide support declarations

- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [WCHAR_H]).stdout
check(src.contains("__WCHAR_TYPE__"))
check(src.contains("#include <stdio.h>"))
check(src.contains("#include <time.h>"))
check(src.contains("wcschr"))
check(src.contains("wmemchr"))
```

</details>

#### SimpleOS pthread header exposes rwlocks for libc++

- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [PTHREAD_H]).stdout
check(src.contains("pthread_rwlock_t"))
check(src.contains("pthread_rwlock_rdlock"))
check(src.contains("pthread_rwlock_wrlock"))
check(src.contains("PTHREAD_MUTEX_RECURSIVE"))
check(src.contains("pthread_mutexattr_settype"))
check(src.contains("pthread_cond_timedwait"))
```

</details>

#### SimpleOS libc exposes next LLVM Support C/POSIX declarations

- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctype = process.run("cat", [CTYPE_H]).stdout
val unistd = process.run("cat", [UNISTD_H]).stdout
check(ctype.contains("isxdigit"))
check(unistd.contains("gethostname"))
check(unistd.contains("getsid"))
check(unistd.contains("alarm"))
check(unistd.contains("getpagesize"))
check(unistd.contains("_SC_PAGE_SIZE"))
```

</details>

#### SimpleOS libc exposes final LLD link runtime declarations

- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stdio = process.run("cat", [STDIO_H]).stdout
val string = process.run("cat", [STRING_H]).stdout
val math = process.run("cat", [MATH_H]).stdout
val mman = process.run("cat", [SYS_MMAN_H]).stdout
check(stdio.contains("vfprintf"))
check(string.contains("wmemcmp"))
check(string.contains("strpbrk"))
check(math.contains("logb"))
check(math.contains("erf"))
check(math.contains("rint"))
check(mman.contains("mprotect"))
```

</details>

#### SimpleOS libc exposes Clang driver rlimit declarations

- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resource = process.run("cat", [SYS_RESOURCE_H]).stdout
val process_wait = process.run("cat", [PROCESS_WAIT_C]).stdout
val statvfs = process.run("cat", [SYS_STATVFS_H]).stdout
val vfs = process.run("cat", [SYS_VFS_H]).stdout
check(resource.contains("RLIMIT_DATA"))
check(resource.contains("RLIMIT_STACK"))
check(resource.contains("RLIMIT_CORE"))
check(resource.contains("typedef unsigned long rlim_t"))
check(resource.contains("RLIM_INFINITY"))
check(resource.contains("struct rlimit"))
check(resource.contains("getrlimit"))
check(resource.contains("setrlimit"))
check(statvfs.contains("f_type"))
check(vfs.contains("#define statfs statvfs"))
check(vfs.contains("#define fstatfs fstatvfs"))
check(process_wait.contains("int getrlimit"))
check(process_wait.contains("int setrlimit"))
check(process_wait.contains("RLIMIT_DATA"))
check(process_wait.contains("RLIMIT_CORE"))
```

</details>

#### SimpleOS libc implements final LLD link runtime surface

- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cxxabi = process.run("cat", [CXXABI_C]).stdout
val libc = process.run("cat", [LIBC_C]).stdout
val dlmalloc = process.run("cat", [DLMALLOC_C]).stdout
val fs = process.run("cat", [FS_C]).stdout
val fork = process.run("cat", [FORK_C]).stdout
val ipc = process.run("cat", [IPC_C]).stdout
val crt0 = process.run("cat", [CRT0_S]).stdout
val string_ext = process.run("cat", [STRING_EXT_C]).stdout
val math_ext = process.run("cat", [MATH_EXT_C]).stdout
check(cxxabi.contains("__cxa_thread_atexit"))
check(cxxabi.contains("align_val_t"))
check(cxxabi.contains("nothrow_t"))
check(cxxabi.contains("int main(int argc, char **argv)"))
check(cxxabi.contains("void _Exit(int status)"))
check(cxxabi.contains("linux_syscall1(60"))
check(libc.contains("int vfprintf"))
check(libc.contains("int mprotect"))
check(libc.contains("running_on_linux_host"))
check(libc.contains("linux_syscall3"))
check(libc.contains("linux_syscall6"))
check(libc.contains("linux_syscall3(0"))
check(libc.contains("linux_syscall3(2"))
check(libc.contains("linux_syscall3(3"))
check(libc.contains("linux_syscall6(9"))
check(libc.contains("linux_syscall3(10"))
check(libc.contains("linux_syscall3(11"))
check(dlmalloc.contains("_linux_host_mmap_pages"))
check(fs.contains("linux_host_stat_syscall"))
check(fs.contains("linux_host_stat_syscall(4"))
check(fs.contains("linux_host_stat_syscall(5"))
check(fs.contains("linux_syscall3(8"))
check(fs.contains("linux_syscall2(77"))
check(fork.contains("linux_syscall0(57"))
check(fork.contains("linux_syscall3(59"))
check(fork.contains("linux_syscall4(61"))
check(ipc.contains("linux_syscall1(22"))
check(ipc.contains("linux_syscall1(32"))
check(ipc.contains("linux_syscall2(33"))
check(crt0.contains("rsp[0] = argc"))
check(crt0.contains("mov     rsi, r13"))
check(crt0.contains("mov     rdx, r14"))
check(string_ext.contains("int wmemcmp"))
check(string_ext.contains("char *strpbrk"))
check(math_ext.contains("double logb"))
check(math_ext.contains("double erf"))
check(math_ext.contains("double rint"))
```

</details>

#### build.shs stages builtins into resource dir

- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
check(src.contains("RES_LIB_DIR"))
check(src.contains("lib/clang/"))
check(src.contains("ninja -C \"$RT_DIR\" builtins"))
check(src.contains("libclang_rt.builtins*.a"))
```

</details>

#### compiler_rt_cmake.cmake exists

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(regular_file_exists(RT_CMAKE))
```

</details>

#### compiler_rt_cmake.cmake enables COMPILER_RT_BUILD_BUILTINS

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_cmake_src()
check(src.contains("COMPILER_RT_BUILD_BUILTINS"))
```

</details>

#### compiler_rt_cmake.cmake disables sanitizers / xray / profile

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_cmake_src()
check(src.contains("COMPILER_RT_BUILD_SANITIZERS"))
check(src.contains("COMPILER_RT_BUILD_XRAY"))
check(src.contains("COMPILER_RT_BUILD_PROFILE"))
```

</details>

#### compiler_rt_cmake.cmake sets COMPILER_RT_OS_DIR to simpleos

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_cmake_src()
check(src.contains("COMPILER_RT_OS_DIR simpleos"))
```

</details>

#### SimpleOS ToolChain README exists

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(regular_file_exists(TOOLCHAIN_README))
```

</details>

#### SimpleOS ToolChain README documents current linker runtime layout

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [TOOLCHAIN_README]).stdout
check(src.contains("share/simpleos/simpleos.ld"))
check(src.contains("lib/clang/20/lib/x86_64-unknown-simpleos"))
check(src.contains("-lclang_rt.builtins-<arch>"))
```

</details>

#### records raw_os_ostream no-localization LLVM Support patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [RAW_OS_OSTREAM_PATCH]).stdout
check(src.contains("_LIBCPP_HAS_LOCALIZATION"))
check(src.contains("raw_os_ostream"))
```

</details>

#### records SimpleOS LLVM Support Path patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [PATH_MAIN_EXECUTABLE_PATCH]).stdout
check(src.contains("__simpleos__"))
check(src.contains("GetMainExecutable"))
```

</details>

#### records no-sstream AssignmentTrackingAnalysis patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [ASSIGNMENT_TRACKING_PATCH]).stdout
check(src.contains("raw_string_ostream"))
check(src.contains("AssignmentTrackingAnalysis.cpp"))
```

</details>

#### records no-sstream SampleProf patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [SAMPLE_PROF_PATCH]).stdout
check(src.contains("raw_string_ostream"))
check(src.contains("SampleProf.h"))
```

</details>

#### records no-iostream instrumentation hex formatting patch

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [INSTRUMENTATION_HEX_PATCH]).stdout
check(src.contains("utohexstr"))
check(src.contains("InstrOrderFile.cpp"))
check(src.contains("AddressSanitizer.cpp"))
```

</details>

#### records no-iostream MemProf node id formatting patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [MEMPROF_HEX_PATCH]).stdout
check(src.contains("Twine::utohexstr"))
check(src.contains("MemProfContextDisambiguation.cpp"))
```

</details>

#### records no-iostream imported function stats formatting patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [IMPORT_STATS_PATCH]).stdout
check(src.contains("format(\"%.4g\""))
check(src.contains("ImportedFunctionsInliningStatistics.cpp"))
```

</details>

#### records no-sstream LLVM MC formatting patch

- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [MC_NO_SSTREAM_PATCH]).stdout
check(src.contains("raw_string_ostream"))
check(src.contains("MCPseudoProbe.cpp"))
check(src.contains("AsmParser.cpp"))
check(src.contains("MasmParser.cpp"))
```

</details>

#### records no-sstream coverage mapping patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [COVERAGE_MAPPING_PATCH]).stdout
check(src.contains("raw_string_ostream"))
check(src.contains("CoverageMapping.h"))
```

</details>

#### records no-iostream TextAPI DylibReader UUID formatting patch

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [TEXTAPI_DYLIBREADER_PATCH]).stdout
check(src.contains("format_hex_no_prefix"))
check(src.contains("DylibReader.cpp"))
```

</details>

#### records no-put-time Clang PPMacroExpansion timestamp patch

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [CLANG_PPMACROEXPANSION_PATCH]).stdout
check(src.contains("formatTimestamp"))
check(src.contains("PPMacroExpansion.cpp"))
check(src.contains("std::put_time"))
```

</details>

#### records no-regex LLD ErrorHandler patch

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [LLD_ERRORHANDLER_PATCH]).stdout
check(src.contains("std::regex"))
check(src.contains("ErrorHandler.cpp"))
check(src.contains("__simpleos__"))
```

</details>

#### records no-iostream/fstream Clang target patch

- check
- check
- check
- check
- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [CLANG_NO_IOSTREAM_PATCH]).stdout
check(src.contains("_LIBCPP_HAS_LOCALIZATION=0"))
check(src.contains("CrossTranslationUnit.cpp"))
check(src.contains("IssueHash.cpp"))
check(src.contains("ThreadSafetyCommon.h"))
check(src.contains("UnsafeBufferUsage.cpp"))
check(src.contains("BareMetal.cpp"))
check(src.contains("LayoutOverrideSource.cpp"))
check(src.contains("CompilerInvocation.cpp"))
check(src.contains("MemoryBuffer"))
check(src.contains("raw_string_ostream"))
```

</details>

#### records Clang target triple stdout flush patch

- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [CLANG_DRIVER_FLUSH_PATCH]).stdout
check(src.contains("Driver.cpp"))
check(src.contains("--print-target-triple"))
check(src.contains("--print-effective-triple"))
check(src.contains("llvm::outs().flush()"))
```

</details>

#### records no-async-unlink LLD filesystem patch

- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [LLD_NO_ASYNC_UNLINK_PATCH]).stdout
check(src.contains("Filesystem.cpp"))
check(src.contains("unlinkAsync"))
check(src.contains("LLVM_ENABLE_THREADS"))
check(src.contains("sys::fs::remove(path)"))
```

</details>

#### records Clang SimpleOS default sysroot link patch

- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [CLANG_DRIVER_SYSROOT_LINK_PATCH]).stdout
check(src.contains("SimpleOS.cpp"))
check(src.contains("build/os/sysroot"))
check(src.contains("share/simpleos/simpleos.ld"))
check(src.contains("lib/clang/20/lib/<triple>"))
check(src.contains("lclang_rt.builtins-<arch>"))
```

</details>

#### records SimpleOS TargetParser no Linux syscall probe patch

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [LLVM_TARGETPARSER_NO_SYSCALL_PATCH]).stdout
check(src.contains("Host.cpp"))
check(src.contains("__simpleos__"))
check(src.contains("syscall"))
```

</details>

#### records AArch64 no-sstream frame helper patch

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = process.run("cat", [LLVM_AARCH64_NO_SSTREAM_PATCH]).stdout
check(src.contains("AArch64LowerHomogeneousPrologEpilog.cpp"))
check(src.contains("raw_string_ostream"))
check(src.contains("std::ostringstream"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/llvm/per_target_build_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS LLVM per-target build (A4/A5)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
