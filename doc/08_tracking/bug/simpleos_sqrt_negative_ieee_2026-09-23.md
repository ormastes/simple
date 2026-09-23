# SimpleOS sqrt negative-input IEEE semantics

Status: source repair complete; admitted target verification deferred.

The SimpleOS libc `sqrt` implementation returned positive zero for every
negative finite input. IEEE/C callers require NaN. The repair returns a
freestanding quiet NaN, explicitly quiets signaling NaN payloads, preserves
negative zero, and preserves positive infinity before entering the existing
bounded Newton loop. This value-level repair makes no fenv or errno claim.

Focused host regression:

```sh
cc -std=c11 -O2 -fno-builtin src/os/libc/simpleos_math.c \
  src/os/libc/test/simpleos_sqrt_ieee_selfcheck.c -o /tmp/simpleos-sqrt-check
/tmp/simpleos-sqrt-check
```

The repaired special-value paths are constant time, allocate no memory, and do
not change the positive finite hot loop.

TODO(simpleos-phase): rerun this value regression in the admitted SimpleOS
native/QEMU environment and record target throughput and maximum RSS when that
phase environment is available.

Assigned follow-up owner: Codex lane
`codex/simpleos-libc-sqrt-finite-0923` replaces the unchanged finite-positive
Newton core. Reproducer: pass binary64 bits `0x0000000000000001` (the smallest
positive subnormal) to this implementation; the current `x * 0.5` initial
guess becomes zero and the next Newton division produces NaN. Extreme finite
magnitudes are also inaccurate. Track both defects in
`doc/08_tracking/bug/simpleos_sqrt_finite_range_2026-09-23.md` on that lane;
neither is claimed fixed by this special-value patch.
