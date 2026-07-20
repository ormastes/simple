# `std.crypto.constant_time` does not export `black_box`

- **Date:** 2026-07-20
- **Area:** `src/lib/common/crypto/constant_time.spl`
- **Severity:** medium (blocks 4 of 5 examples in the file).
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/black_box_spec.spl --no-session-daemon
```

```
✗ is identity on integer inputs
    semantic: function `black_box` not found
✗ ct_eq_bytes returns true for equal buffers
    semantic: function `black_box` not found
✗ ct_eq_bytes returns false on byte difference
    semantic: function `black_box` not found
✓ ct_eq_bytes returns false on length difference
✗ ct_eq_bytes handles empty buffers
    semantic: function `black_box` not found
```

5 examples, 4 failures.

## Root-cause hypothesis

`test/unit/lib/crypto/black_box_spec.spl:16` imports
`use std.crypto.constant_time.{black_box}`. The module file
`src/lib/common/crypto/constant_time.spl` exists and defines
`constant_time_compare` and `constant_time_compare_bytes` only
(`grep -n "^fn " src/lib/common/crypto/constant_time.spl`) — there is no
`black_box` function anywhere in `src/lib/common/crypto/` or
`src/os/crypto/`. `black_box` (an optimization-barrier helper, typically
used so a compiler/JIT can't constant-fold or dead-code-eliminate
timing-sensitive test code) has never been implemented; this is a genuinely
missing function, not a rename.

The one passing example ("returns false on length difference") happens not
to call `black_box` on its success path.

## What NOT to do

Do not remove/soften the 4 failing `it` blocks — `black_box` is a real,
useful primitive for constant-time testing infrastructure and its absence
is a genuine gap.

## Affected specs

- `test/unit/lib/crypto/black_box_spec.spl` (4 of 5 examples)
