# crt0 and libc both define `environ` — duplicate symbol breaks the lld link

- **ID:** simpleos-crt0-environ-duplicate-symbol-2026-08-06
- **Status:** FIXED (2026-08-06)
- **Severity:** HIGH — failed `bin/lld` in the cross toolchain build (lane C1)
- **Owner path:** `src/os/libc/simpleos_crt0.S`
- **Related:** `simpleos_libc_leaks_simple_runtime_syms_2026-08-06.md` (same lane,
  different root cause)

## Symptom

After the libc/Simple-runtime split unblocked CMake configure, the cross build
compiled 2,247 of 2,944 targets and failed on exactly one:

```
FAILED: bin/lld
ld.lld: error: duplicate symbol: environ
>>> defined at .../build/os/sysroot/lib/crt0.o:(.bss+0x0)
>>> defined at simpleos_process.c
>>>            simpleos_process.o:(.data+0x0) in archive .../libsimpleos_c.a
```

## Root cause — a fix in one direction that broke the other

`environ` had two owners:

- `src/os/libc/simpleos_crt0.S` — `.globl environ` with 8 bytes of `.bss`
- `src/os/libc/simpleos_process.c:26` — `char **environ = _env_storage;`

crt0's definition was itself a **defensive fix for the opposite bug**, and its
comment recorded it: `environ` was originally `.weak` in crt0 with no libc
definition anywhere, so it resolved to address 0 and crt0's publish store
`mov [environ], r14` faulted writing to NULL (ring-3 #PF at `_start`, errcode
`P|W|U`, `cr2=0`). Giving it real storage fixed that — but as `.globl`.

Once libc gained its own strong definition, the two collided. `crt0.o` is
linked **explicitly** on every link line (not pulled from an archive), so the
clash is unconditional: every C/C++ executable that pulls `simpleos_process.o`
(anything calling `getenv`/`setenv` — clang and lld both do) fails to link.

## Fix

`.globl environ` → `.weak environ` in `simpleos_crt0.S`, with the full
two-directional history recorded in the comment so neither side gets "fixed"
back into a regression.

Weak is the binding that satisfies both requirements at once:
- libc's process object linked (normal case) → its **strong** definition wins,
  and crt0 publishes `envp` into the real libc pointer, which is the correct
  behavior;
- libc's process object not linked → crt0's weak storage keeps the publish
  store off NULL.

Verified: `nm simpleos_crt0.o | grep environ` → `W environ`.

## Lesson

A defensive definition added because a symbol was *missing* becomes a duplicate
the moment the real owner supplies it. When crt0-style startup code must both
**publish** and **survive the absence of** a libc symbol, the binding is `.weak`
— never `.globl`. Both failure modes here produced the same class of hard stop
(NULL fault at `_start` one way, link failure the other), so the comment now
documents both directions explicitly.
