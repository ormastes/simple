# SimpleOS libc: float functions cannot be ported to pure Simple (f64 unreliable)

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — f64 premise does NOT reproduce on the seed's two arms; still OPEN

- **measured** (Windows Rust seed v1.0.0-rc.1, `bin/simple run`, under BOTH
  `SIMPLE_EXECUTION_MODE=interpret` and `=jit`): nested f64 return
  `outer(2.0)` -> `3.25`, struct-field f64 return `getv(P(v: 1.125))` ->
  `1.125`, accumulate loop -> `0.5`, and `"2.75".to_f64()` -> `2.75`.
- **inferred**: this weakens but does not retire the blocker; SMF and
  native/freestanding were not exercised and no float libc function was ported.
- **inferred**: left OPEN; remeasure f64 rather than inheriting the premise.

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

## 2026-09-22 progress — decimal-only staging parser

The f64 interpreter prerequisite is strong enough to execute a decimal-only
staging parser toward `strtod`/`strtof`. The new
`src/os/libc/simpleos_stdlib_float.spl` implements decimal prefix parsing,
end-index reporting (the pointer-free `endptr` equivalent), optional signs,
fractions, exponent backtracking, and saturating hostile-exponent handling.
It is not a stub or a hosted-libc wrapper, but it is not yet a C-compatible
replacement: hexadecimal floats, inf/nan, locale, errno/range reporting, and
guaranteed correct rounding remain unsupported.

Focused evidence:

- `test/01_unit/os/libc/libc_stdlib_float_spec.spl`: all 11 examples pass in
  0.402 s test time. The available runner identified itself as a Rust bootstrap
  seed, so this is syntax/behavioral evidence only, not self-hosted or release
  admission. The bounded invocation used 3.65 s wall and 327,656 KiB maximum
  RSS including compiler/test-runner startup. The regressions cover compensated
  extreme exponents, binary32 rounding, and finite-range boundaries. The
  binary32 cases include
  exact integer ties-to-even plus the smallest subnormal and largest finite
  oracle values. The binary64 cases distinguish largest-finite/min-subnormal
  from overflow/underflow without claiming general correctly rounded strtod.
- `test/fixtures/simpleos_libc_strtod_probe.spl`: the normalized revision
  completed 10,001 calls and printed `PASS` in 0.05 s wall with 41,680 KiB
  maximum RSS on the aarch64 Linux seed/JIT runner. This bounds the staging
  parser's current loop and allocation behavior, but is not admitted-native or
  SimpleOS-target performance evidence.
- Added production source is 4,729 bytes; test and probe source add 4,822
  bytes. Compiled-object size is
  currently unmeasurable because native-build
  fails closed before object emission: the runtime manifest requires missing
  `src/runtime/runtime_file_view.c` (observed max RSS 131,536 KiB).  This is an
  existing runtime-input blocker, not a parser failure.

The ticket remains OPEN: the C twins stay in place until native/SimpleOS target
parity is measurable, and the larger `simpleos_math*.c` plus printf-float ports
remain outstanding.  The self-hosted f64 call-result gate also cannot run
until a non-seed self-hosted compiler is available.

TODO(simpleos-phase): once an admitted self-hosted phase compiler and SimpleOS
QEMU environment are available, rerun the focused spec with that compiler,
measure native object size and parser throughput/RSS, then exercise the same
vectors in the guest before replacing either C twin.

## 2026-09-23 decimal correct-rounding follow-up

The follow-on parity surface is deliberately exact and narrower than all of C
`strtod`: accepted decimal prefixes (ASCII whitespace/sign, decimal point, and
signed decimal exponent) must round once to binary64 or binary32 using
round-to-nearest, ties-to-even. It covers signed zero, subnormal/normal and
finite/infinity value classes plus C-compatible malformed-exponent end index.
Hexadecimal floats, `inf`/`nan` spellings and payloads, locale radix, `errno`,
floating-point exception flags, and directed rounding remain owned by the C
provider; therefore this follow-up does not authorize replacing that provider.

The exact path retains at most 1,200 significant decimal digits in base-2^30
BigNat limbs and a sticky bit. The most precise binary64 boundary is half the
smallest subnormal, `2^-1075`. A dyadic midpoint numerator has at most 54 bits;
after multiplying by at most `5^1075`, its terminating decimal has at most 768
significant digits (though as many as 1,075 fractional places). Binary32's
corresponding denominator bound is `2^150`; positive-power boundaries need no
more than 309 significant decimal digits. Therefore 1,200 retained significant
digits plus a nonzero-tail sticky bit determine every midpoint direction for
both formats. The adversarial spec constructs an exact binary64 midpoint followed
by more than 1,200 zero digits and a final one; removing that one selects the
even lower value, while its sticky presence selects the upper value. This is a
falsifiable cap rather than a heuristic precision claim.

Inputs receive one grammar scan plus, only on the BigNat slow path, one
bounded-significand reconstruction pass; total parse work remains O(n) and
preserves `endptr` semantics. Live
BigNat mantissa storage is capped by the 1,200-digit prefix (about 4,000 bits);
range-bounded power-of-five denominators can reach about 5,060 bits.
Exact small integers and binary fractions use an allocation-light fast path;
other inputs use bounded rational division and ties-to-even.

The first mixed 20,000-call probe exposed and caused removal of per-digit
BigNat allocation from the ordinary path. That pre-fix probe failed its checksum
gate and used 2.34 s wall / 537,732 KiB maximum RSS including seed compilation;
it is retained as negative evidence, not a performance pass. The amended parser
stores only source indices and scalar state for ordinary inputs and constructs
BigNat state only after the fast path declines the value.

TODO(simpleos-decimal-parity-perf): in a fresh verification session, rerun
`test/fixtures/simpleos_libc_float_parity_probe.spl` and compare parser-only
throughput/allocation against the #1356 10,001-call baseline. This session hit
the mandatory three-cycle cap before the allocation repair could be rerun.

TODO(simpleos-decimal-parity-admission): after an admitted self-hosted compiler
and SimpleOS QEMU image exist, run the adversarial rounding spec and a bounded
throughput/RSS comparison in the guest. Keep the C provider until the excluded
grammar/range-reporting surfaces above have their own parity implementation.
