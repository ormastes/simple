# `os.crypto.pem` `pem_encode` chain calls a `.bytes()` method on an `array` value that doesn't support it

- **Date:** 2026-07-20
- **Area:** `src/os/crypto/pem.spl` (and/or a base64 helper it calls)
- **Severity:** medium (whole spec file cannot load; 0 examples run).
- **Status:** OPEN — root cause not fully localized, needs a source-owner
  follow-up (see caveat below).

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/pem_rfc7468_kat_spec.spl --no-session-daemon
```

```
error: semantic: method `bytes` not found on type `array` (receiver value:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
   21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])
error: test-runner: no examples executed
```

## Repro

```
test/unit/lib/crypto/pem_rfc7468_kat_spec.spl:27  fn _der_32() -> [u8]:
    var out: [u8] = []
    var i = 0
    while i < 32:
        out.push(i.to_u8())
        i = i + 1
    out
```

The receiver value in the error (`[0, 1, ..., 31]`) is exactly `_der_32()`'s
output, so the failure happens somewhere in the call chain starting from
`pem_encode(label, _der_32())` (`test/unit/lib/crypto/pem_rfc7468_kat_spec.spl:20`
imports `pem_encode, pem_decode, pem_decode_all, PemBlock` from
`os.crypto.pem`).

## Root-cause hypothesis

There is no literal `.bytes(` call anywhere in the spec file itself
(`grep -n "bytes(" test/unit/lib/crypto/pem_rfc7468_kat_spec.spl` is empty),
and no literal `.bytes(` call in `src/os/crypto/pem.spl`
(`grep -n "\.bytes(" src/os/crypto/pem.spl` is empty). The call must
therefore originate inside a helper `pem_encode` transitively calls (likely
its base64 encoding step) that invokes `.bytes()` on an already-`[u8]` array
value — a method that array values don't support at the current call site's
inferred type. This was not fully localized within this triage pass (the
call is not a direct textual match anywhere searched); flagging with the
exact receiver value and entry point (`pem_encode`) so a source owner can
trace the actual call site with a debugger/print-trace rather than grep.

## What NOT to do

Do not add/change a `.bytes()` call in the spec — the spec doesn't call it;
the bug is inside the library's encode path.

## Affected specs

- `test/unit/lib/crypto/pem_rfc7468_kat_spec.spl` (0 examples executed —
  load failure)
