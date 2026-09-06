# `F_ADD_SEALS` undeclared in runtime_dynload.c — every native-build fails (2026-08-24)

**Date:** 2026-08-24
**Status:** FIXED in this commit
**Severity:** Critical — `origin/main` could not native-build ANYTHING on this host
**Platform:** x86_64-unknown-linux-gnu, glibc, clang

## Symptom

Any `bin/simple native-build <anything>` fails at the runtime link step:

```
error: Hosted native linking failed: Runtime compilation failed:
       Failed to compile runtime_dynload.c:
src/runtime/runtime_dynload.c:60:25: error: use of undeclared identifier 'F_ADD_SEALS'
                                     use of undeclared identifier 'F_SEAL_GROW'
                                     use of undeclared identifier 'F_SEAL_SEAL'
```

Affects TWO files, `src/runtime/runtime_dynload.c:60` and
`src/runtime/runtime_native.c:7598`. Introduced with the artifact-sealing work (`0ea21e73c95 fix(sffi): bind Linux
loads to sealed artifacts`), which added an `fcntl(snapshot, F_ADD_SEALS, ...)`
call without the declarations it needs.

## Proven pre-existing, not caused by the finder's own edits

Measured by stashing all local changes and rebuilding from the clean tree:

```
RC_WITHOUT_MY_EDIT=1
undeclared identifier 'F_ADD_SEALS'
undeclared identifier 'F_SEAL_GROW'
undeclared identifier 'F_SEAL_SEAL'
```

## Why the C-runtime gate did not catch it

`scripts/check/check-c-runtime-compiles-push.shs` runs `$CC -fsyntax-only` over
`src/runtime/*.c`, which is exactly the check that fails here — so this should
have been blocked at push time. Whoever landed the sealing change either did not
run it or pushed with `--no-verify`. The guard itself is sound; this is a
process gap, and it is the second time in this file's history that a
"structurally clean tree that does not compile" reached `main`.

## Fix

`F_ADD_SEALS` and the `F_SEAL_*` flags are Linux-specific fcntl commands. glibc's
`<fcntl.h>` exposes them only under `_GNU_SOURCE` and only on new enough
releases.

**Including `<linux/fcntl.h>` does NOT work** and was tried first — it pulls in
`asm-generic/fcntl.h`, which redefines `struct flock` against the glibc
`<fcntl.h>` already included above:

```
/usr/include/asm-generic/fcntl.h:193:8: error: redefinition of 'flock'
```

So the constants are defined directly, each behind `#ifndef`, inside the
existing `#if defined(__linux__)` block. They are stable UAPI values the kernel
cannot change without breaking every existing binary, and the `#ifndef` guards
mean a toolchain that does declare them keeps its own definitions.

Verified: `clang -fsyntax-only -Isrc/runtime src/runtime/runtime_dynload.c`
exits **0** (status read directly into a variable on the line after the command,
never through a pipe).

## Verification

The repo's own gate, which is the authority here:

```
$ sh scripts/check/check-c-runtime-compiles-push.shs
before: FAIL — 1 file(s) failed to compile: src/runtime/runtime_native.c
        (117 compiled clean, 2 skipped for unavailable external dependencies)
after:  PASS — 118 file(s) compiled, 0 errors
        (2 skipped for unavailable external dependencies)
```

`C_RUNTIME_GATE_RC=0`, read directly into a variable on the line after the
command. Note the before-run: fixing only `runtime_dynload.c` moved the failure
to `runtime_native.c`, which carries the identical defect — a reminder that the
first green file is not a green tree.

## RESOLVED 2026-08-26

`F_ADD_SEALS` / `F_SEAL_WRITE` / `F_SEAL_GROW` are glibc `__USE_GNU` symbols, so
`<fcntl.h>` alone does not declare them. Both owners called `fcntl(snapshot,
F_ADD_SEALS, ...)` beside a `syscall(SYS_memfd_create, ...)` — Linux-only code
that had never been given the Linux-only feature macro.

Fixed by prepending the guard `src/runtime/runtime_thread.c:1-3` already
established, rather than inventing a new idiom:

    #if defined(__linux__) && !defined(_GNU_SOURCE)
    #define _GNU_SOURCE
    #endif

Applied to `src/runtime/runtime_native.c` and `src/runtime/runtime_dynload.c`.
`<linux/fcntl.h>` was considered and rejected — it conflicts with `<fcntl.h>`
and would not match the existing convention.

`clang -fsyntax-only` on both owners: **rc=0** (one pre-existing
`ATOMIC_VAR_INIT` deprecation warning in `runtime_native.c`, untouched and
unrelated).

## Gate evidence

    sh scripts/check/check-c-runtime-compiles-push.shs

| when | verdict |
|---|---|
| before | `FAIL — 2 file(s) failed to compile: src/runtime/runtime_dynload.c src/runtime/runtime_native.c (115 compiled clean, 2 skipped)` rc=1 |
| after | `PASS — 117 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)` rc=0 |

## Prevention

No new gate is needed and none should be added: `check-c-runtime-compiles-push.shs`
is MANDATORY per `.claude/rules/vcs.md` and it caught both of these correctly —
it was honestly RED the whole time. The failure was process, not coverage: a
mandatory gate was left red across sessions instead of blocking. The durable fix
is that a red mandatory gate blocks a push, which is already the stated rule.

Note for the next reader: `-fsyntax-only` does not link, so a
declared-but-never-defined symbol still passes this gate. That limit is real and
is why the unresolved-runtime-symbols guard exists separately.
