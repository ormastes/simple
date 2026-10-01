# SimpleOS sqrt finite-range accuracy

Status: source repair complete; admitted target verification deferred.

Owner: Codex lane `codex/simpleos-libc-sqrt-finite-0923`.

The former 30-step Newton loop initialized its estimate as `x * 0.5`. For the
smallest positive binary64 subnormal (`0x0000000000000001`) that expression
underflows to zero, so the subsequent division produces NaN. Its fixed
iteration/tolerance scheme also loses substantial accuracy at extreme finite
magnitudes.

The repair uses musl's fixed-point Goldschmidt binary64 square-root core and
128-entry reciprocal-square-root table. It normalizes subnormals and produces
correct round-to-nearest values across the finite positive range without
division, allocation, input-sized storage, or data-dependent iteration.

Focused regression covers the smallest subnormal, largest subnormal, smallest
normal, largest finite value, special values, and exact squares. The core uses
constant stack state and a 256-byte read-only table; it replaces up to 30
floating divisions with a bounded sequence of integer multiplies. A separate
host oracle regression compares 100,000 deterministic positive finite bit
patterns with the platform libm result.

TODO(simpleos-phase): rerun the focused regression in the admitted SimpleOS
native/QEMU environment, compare representative finite vectors against the
admitted phase-2 compiler/libm oracle, and record throughput plus maximum RSS.
