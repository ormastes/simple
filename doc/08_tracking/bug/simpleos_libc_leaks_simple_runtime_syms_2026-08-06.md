# SimpleOS libc leaks Simple-runtime symbols into every C/C++ link

- **ID:** simpleos-libc-leaks-simple-runtime-syms-2026-08-06
- **Status:** FIXED (2026-08-06)
- **Severity:** HIGH — blocked the entire cross LLVM/clang toolchain build (lane C1)
- **Owner path:** `src/os/libc/`
- **Related:** `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md` (lane C1)

## Symptom

`sh src/os/port/llvm/build.shs cross` failed at CMake configure time with a
misleading message that named the wrong subsystem entirely:

```
CMake Error at cmake/modules/CheckCompilerVersion.cmake:88 (message):
  libstdc++ version must be at least 7.4.
```

and, after the first fix, the equally misleading:

```
CMake Error at cmake/modules/CheckAtomic.cmake:59 (message):
  Host compiler appears to require libatomic, but cannot find it.
```

Neither message is true. The host has clang 20.1.8 / gcc 13.3
(`_GLIBCXX_RELEASE=13`), and the SimpleOS target links both 32-bit and 64-bit
`std::atomic` correctly. **Both messages are `check_cxx_source_compiles`
reporting "the probe did not build" — CMake cannot distinguish "feature
missing" from "link failed for an unrelated reason".** The real error is only
visible in `CMakeFiles/CMakeConfigureLog.yaml`:

```
ld.lld: error: undefined symbol: rt_array_len
>>> referenced by simpleos_libc.c
>>>               simpleos_libc.o:(rt_array_len_safe) in archive .../libsimpleos_c.a
ld.lld: error: undefined symbol: rt_array_new
ld.lld: error: undefined symbol: rt_string_new
ld.lld: error: undefined symbol: rt_array_push
>>>               simpleos_libc.o:(simpleos_runtime_cli_get_args) in archive .../libsimpleos_c.a
```

## Root cause

Two independent defects, the second masked by the first.

**Defect 1 — layering violation, archive-member granularity.**
`src/os/libc/simpleos_libc.c` contained the Simple-runtime CLI-argv bridge
(`rt_array_len_safe`, `rt_set_args`, `spl_init_args`, `rt_cli_arg_count`,
`rt_cli_arg_at`, `rt_cli_get_args`, `rt_get_args`, `sys_get_args`) in the SAME
translation unit as core libc (`write`, `exit`, stdio, …). Those functions call
`rt_array_new` / `rt_array_push` / `rt_array_len` / `rt_string_new`, which are
provided by the **Simple language runtime**, not by libc.

Linkers pull static-archive members at **object** granularity. Any plain C or
C++ program that referenced *anything* in `simpleos_libc.o` — i.e. every program
— dragged the Simple-runtime dependency in with it and failed to link. A C/C++
consumer of a C library must never require the Simple runtime.

**Defect 2 — stale derived archive.** `build/os/sysroot/lib/libm.a` is a plain
copy of `libsimpleos_c.a` (`src/os/port/llvm/sysroot.shs:266`). The staged copy
was from 2026-07-30 and still contained the pre-fix `simpleos_libc.o`. Because
the link line places `-lm` *before* `-Wl,--start-group -lc++ -lsimpleos_c -lm`,
the stale object was pulled first and the failure persisted verbatim after
Defect 1 was fixed — looking exactly like the fix had not worked.

## Fix

1. Moved the whole bridge block out of `simpleos_libc.c` into a new dedicated
   translation unit `src/os/libc/simpleos_cli_args.c`, with a header comment
   stating why it must stay isolated. Added it to `C_SRCS` in
   `src/os/libc/Makefile`. `crt0.S` takes only a **weak** reference to
   `rt_set_args`, and a weak undefined reference does not pull an archive
   member, so a C-only link stays clean.
2. Rebuilt `libsimpleos_c.a` and re-staged **both** it and its `libm.a` copy
   into the sysroot.

No behavior change for real consumers: a Simple-targeted program that
references `rt_cli_get_args` still pulls the object, and links
`libsimple_runtime.a` which defines the `rt_*` symbols.

## Evidence

Before (core object carried the dependency), after:

```
$ nm -u simpleos_libc.o | grep -E 'rt_array|rt_string'
NONE (good)
$ nm -u simpleos_cli_args.o | grep -cE 'rt_array|rt_string'
4
```

The exact CMake probe link, replayed verbatim, before → `exit 1` with the four
undefined symbols; after → `EXACT_PROBE_LINK_RC=0`.

Cross configure then completed (`build.ninja` present, no CMake error) and the
build proceeded into `ninja -C build/os/llvm/cross-x86_64-unknown-simpleos
clang lld`.

## Lesson (generalizable)

- A CMake `check_*_compiles` FATAL_ERROR names the **feature it was probing**,
  never the reason the probe failed. Always read
  `CMakeFiles/CMakeConfigureLog.yaml` for the real linker diagnostic before
  believing the message. Two different messages here ("libstdc++ too old",
  "requires libatomic") had one identical cause.
- When a fix "doesn't take", check for **derived copies** of the artifact you
  fixed. `libm.a` being a `cp` of `libsimpleos_c.a` meant one stale file
  reproduced the original error perfectly.
- Library layering is enforced by the linker at object granularity: putting a
  higher-layer bridge in a widely-referenced low-layer TU makes the dependency
  effectively mandatory for every consumer.
