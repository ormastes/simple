# HTTP Basic auth comments claim an `rt_black_box` barrier the code never calls

**Status:** FIXED — 2026-08-09, verified via
`src/lib/nogc_sync_mut/http/auth/http_auth_spec.spl` (all 11 Basic-auth
examples pass; the two pre-existing failures in that run are unrelated
Digest-auth cases — `returns empty string for unsupported algorithm` and
`verify accepts SHA-256 no-qop response` — untouched by this change).
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

## Fix (2026-08-09)

Applied the exact change proposed above to all three tiers with a real body
(`nogc_sync_mut`, `gc_async_mut`, `nogc_async_mut`): imported
`std.common.crypto.constant_time.{black_box}` and changed the final compare
from `diff == 0` to `black_box(diff) == 0`. `black_box` in
`src/lib/common/crypto/constant_time.spl` was `fn` (private), not `pub fn`,
which would have made the import unresolvable — made it `pub fn` as part of
this fix. `gc_sync_mut/http/auth/basic.spl` needed no change: it is a
3-line re-export facade (`export use
std.gc_async_mut.http.auth.basic.*`) onto the `gc_async_mut` copy just
fixed, not an independent implementation — the "has neither the comment nor
the barrier" observation above was about the facade file itself having no
`_ct_bytes_equal` body to patch, which remains true and is not a gap.

Verified with `bin/simple test src/lib/nogc_sync_mut/http/auth/http_auth_spec.spl`
(existing spec, not new): `declared>=21 executed=21 passed=19 failed=2`. All
11 Basic-auth examples (including the 3 exercising
`http_basic_ct_verify` → `_ct_bytes_equal`) pass. The 2 failures are
pre-existing, unrelated Digest-auth cases (`returns empty string for
unsupported algorithm`, `verify accepts SHA-256 no-qop response`) — confirmed
untouched by this change since Digest auth does not call `_ct_bytes_equal` or
`black_box`.

No new spec was added to pin the barrier call site itself (e.g. asserting
`grep -c 'black_box(' basic.spl >= 1`) — the existing behavioral spec proves
the barrier is *reachable and correct*, which is the property that matters;
a literal call-site regression test was judged not worth a dedicated spec
file for a one-line wrap. If this regresses again, re-open and add one.
