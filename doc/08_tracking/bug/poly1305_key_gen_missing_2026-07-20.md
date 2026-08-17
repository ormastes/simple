# `std.crypto.poly1305` does not export `poly1305_key_gen` (RFC 8439 §2.6.2)

- **Date:** 2026-07-20
- **Area:** `src/lib/common/crypto/poly1305.spl`
- **Severity:** medium (missing function, not a wrong-value bug; blocks 2 of
  9 examples).
- **Status:** FIXED 2026-08-17.

## Resolution (2026-08-17)

`poly1305_key_gen(key, nonce)` implemented per RFC 8439 §2.6.2 — first 32
bytes of the ChaCha20 keystream at **block counter 0** — in
`src/lib/common/crypto/poly1305.spl:293-311`, and mirrored into
`src/os/crypto/poly1305.spl` (the original grep found zero hits in *both*
modules, so fixing only one would have left the os copy broken).

Measured with `bin/simple run <spec> --no-session-daemon`, same tree, same
binary (`bin/release/x86_64-unknown-linux-gnu/simple`):

| | `poly1305_spec.spl` |
|---|---|
| before | `executed=9 passed=7 failed=2` (`function poly1305_key_gen not found`) |
| after | `executed=9 passed=9 failed=0` |

The RFC 8439 §2.6.2 one-time-key KAT passes, so the helper is byte-correct,
not merely present.

Class-detection spec:
`test/01_unit/lib/crypto/poly1305_key_gen_class_spec.spl` (4/4). It pins the
two silent regressions a look-alike fix allows: deriving at block counter 1
(still 32 plausible bytes, breaks every AEAD tag) and the std/os module copies
drifting apart. **Ablation:** flipping counter 0→1 in the implementation takes
that spec from `passed=4 failed=0` to `passed=1 failed=3`; restoring it
returns 4/4. The counter check carries its own guard example asserting the
counter-0 and counter-1 keystreams really differ, so it cannot pass vacuously.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/poly1305_spec.spl --no-session-daemon
```

```
✗ poly1305_key_gen produces the RFC 8439 §2.6.2 expected one-time key
    semantic: function `poly1305_key_gen` not found
✗ poly1305_key_gen always returns exactly 32 bytes
    semantic: function `poly1305_key_gen` not found
```

2 examples, 2 failures in this describe block; 7 other examples in the file
(poly1305_mac correctness) pass (Passed: 7, Failed: 2 overall).

## Root-cause hypothesis

`test/unit/lib/crypto/poly1305_spec.spl:19` imports
`use std.crypto.poly1305.{poly1305_mac, poly1305_key_gen}`. `poly1305_mac`
resolves fine. `poly1305_key_gen` — the RFC 8439 §2.6.2 helper that derives
a one-time Poly1305 key from a ChaCha20 key + nonce via the ChaCha20 block
function — is not defined anywhere:

```
grep -rn "fn.*key_gen" src/lib/common/crypto/*.spl src/os/crypto/*.spl
```

returns nothing for poly1305. Both `src/lib/common/crypto/poly1305.spl` and
its `src/os/crypto/poly1305.spl` mirror only define `poly1305_init`,
`poly1305_block`, `poly1305_finalize`, `poly1305_mac` — no key-derivation
helper. This is a genuinely missing implementation, not a rename: the
function has never existed under any name in this module.

## What NOT to do

Do not remove/soften the two `it` blocks — `poly1305_key_gen` is a real,
separately-testable RFC 8439 primitive and its absence is a real gap in the
`std.crypto.poly1305` public surface, not a stale test.

## Affected specs

- `test/unit/lib/crypto/poly1305_spec.spl` (2 of 9 examples)
