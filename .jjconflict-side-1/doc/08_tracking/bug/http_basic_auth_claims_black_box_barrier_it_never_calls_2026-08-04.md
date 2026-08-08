# HTTP Basic auth comments claim an `rt_black_box` barrier the code never calls

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** medium — the credential compare in three runtime tiers is
documented as timing-safe on the strength of a barrier that is not in the
emitted code, so a reader auditing for timing side channels gets a false pass

## Symptom

`_ct_bytes_equal` in the HTTP Basic auth path is the function that compares a
presented password against the stored one. Its header comment states:

```
# Uses XOR-accumulate so the loop cannot be short-circuited by the optimizer.
# Wraps the accumulator through rt_black_box at the end.
```

and the body carries a second comment on the same claim:

```
    # rt_black_box prevents the optimizer from turning the XOR loop into an
    # early-exit branch. The cast via == 0 does the final boolean test.
    diff == 0
```

`rt_black_box` is never called. Minimal repro — mentions versus actual call
sites, across every copy:

```sh
$ for f in src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut,gc_sync_mut}/http/auth/basic.spl; do
    echo "$f: calls=$(grep -c 'rt_black_box(' $f) mentions=$(grep -c 'rt_black_box' $f)"
  done
src/lib/nogc_sync_mut/http/auth/basic.spl: calls=0 mentions=2
src/lib/gc_async_mut/http/auth/basic.spl:  calls=0 mentions=2
src/lib/nogc_async_mut/http/auth/basic.spl: calls=0 mentions=2
src/lib/gc_sync_mut/http/auth/basic.spl:   calls=0 mentions=0
```

Expected: `mentions` implies at least one `calls`. Actual: zero call sites in
all four, while three of the four assert the barrier is applied.

## Root cause

`src/lib/nogc_sync_mut/http/auth/basic.spl:27-37` (and the identical bodies in
the `gc_async_mut` and `nogc_async_mut` copies) end with a bare `diff == 0`.
Nothing routes `diff` through an opaque call, so the compiler is free to
recognise the XOR-accumulate as "is any byte different" and rewrite it into an
early-exit branch — exactly the data-dependent timing the accumulate loop is
written to avoid. The comment describes an intended implementation that was
never written, or was written and later dropped; either way the code and its
documentation disagree, and the documentation is the reassuring one.

The barrier itself is real and available: the runtime registers `rt_black_box`
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:600`, implemented at
`interpreter_extern/file_io.rs:460`), and as of this change
`src/lib/common/crypto/constant_time.spl` exposes it as `black_box(value: i64)`
with the RFC-style usage note. The fix is to import that and wrap the final
compare:

```
use std.common.crypto.constant_time.{black_box}
...
    black_box(diff) == 0
```

## Why not fixed now

The four `http/auth/basic.spl` copies are outside the `test/01_unit/lib/` scope
this session was working, and no spec in the tree exercises `_ct_bytes_equal` —
so the change could be made but not *proved*, and an unverified edit to a
credential-comparison path in four runtime tiers is worse than a filed defect.
It also wants doing as one sweep across all four copies (the `gc_sync_mut` one
has neither the comment nor the barrier, so it needs the same fix without the
misleading comment to flag it), plus a spec that pins the barrier is present —
which is the only thing that would stop this regressing again.
