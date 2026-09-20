# SimpleOS libc: float functions cannot be ported to pure Simple (f64 unreliable)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — f64 premise does NOT reproduce on the seed's two arms; still OPEN
- **measured** (Windows Rust seed v1.0.0-rc.1, `bin/simple run`, under BOTH `SIMPLE_EXECUTION_MODE=interpret` and `=jit`): nested f64 return `outer(2.0)` -> `3.25`, struct-field f64 return `getv(P(v: 1.125))` -> `1.125`, accumulate loop -> `0.5`, `"2.75".to_f64()` -> `2.75`. No 0.0, no nested-return corruption, no call-boundary garbage.
- **inferred**: this weakens but does not retire the blocker — the entry also indicts the SMF and native/freestanding backends, neither of which is exercisable on this Windows host, and no float libc function has actually been ported.
- **inferred**: left OPEN. Whoever picks this up should re-measure the f64 claim first rather than inheriting it.

Date: 2026-06-28

Lane: `.spipe/simpleos-alpine-harden-musl-busybox` (AC-5)

## Summary

The pure-Simple libc port (string/mem/ctype/stdlib-integer) is complete and
green. The remaining C libc functions split into two groups that **cannot**
currently be implemented in pure Simple:

### 1. Floating-point functions — blocked by unreliable f64

`strtod`, `strtof` (`simpleos_stdlib_ext.c`), all of `simpleos_math.c` /
`simpleos_math_ext.c`, and `simpleos_printf_float.c`.

f64 is untrustworthy across interpreter / SMF / runner / native backends
(interp returns 0.0; nested-return corruption; call-boundary garbage — see the
standing f64 feature-lag notes). A pure-Simple `strtod` would parse to wrong
values and its spec could not assert correctness. **Blocked until f64 is
reliable on the interpreter test path.** Keep the C implementations.

### 2. Syscall / hardware-backed — not "pure computation"

`alloc`/`dlmalloc` (mmap/sbrk), `fs`, `fork`, `process`, `signal`, `pthread`,
`poll`/`epoll`, `time`, `ipc`, `eventfd`, `inotify`, `timerfd`, `signalfd`,
`setjmp`, `syscall`. These require kernel syscalls / hardware access and are
correctly C (or thin Simple-over-syscall wrappers), not pure Simple — per the
project rule "make them pure Simple if no perf/hw problem; else file a bug."

## Done in this lane (pure Simple, interpreter-verified)

`simpleos_string.spl` + `simpleos_stdlib.spl` + `simpleos_stdio.spl` +
`simpleos_string_copy.spl` (strcpy/strncpy/strcat/strncat/strdup/strndup/strnlen)
+ `simpleos_string_search.spl`
(strstr/strspn/strcspn/strpbrk/memchr/memrchr/strcasecmp/strncasecmp/strtok_r/strerror)
+ `simpleos_stdlib_num.spl` (strtoul/strtoll/strtoull/div/ldiv/lldiv/rand).
`memmove` is subsumed by value-returning `memcpy` (no in-place overlap in the
value-semantics model).

## Acceptance for closure

- f64 reliable on the interpreter test path → port `strtod`/`strtof`/`math`
  with KAT specs, then delete the C twins (keep-C-until-parity policy).
- Syscall group: confirm each is a thin Simple-over-syscall wrapper or
  legitimately C; no pure-Simple obligation.

