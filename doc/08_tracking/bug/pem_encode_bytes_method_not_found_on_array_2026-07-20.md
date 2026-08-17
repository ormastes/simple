# `os.crypto.pem` `pem_encode` chain calls a `.bytes()` method on an `array` value that doesn't support it

- **Date:** 2026-07-20
- **Area:** `src/os/crypto/pem.spl` (and/or a base64 helper it calls)
- **Severity:** medium (whole spec file cannot load; 0 examples run).
- **Status:** FIXED 2026-08-17.

## Root cause (2026-08-17) — localized

`src/os/crypto/pem.spl` was written against a **list-of-i64 base64 API that no
longer exists**. Two independent breakages, both at the import line
(`pem.spl:21-22` before the fix):

1. `base_encoding.base64.base64_encode` has signature `(data: text) -> text`
   (`src/lib/common/base_encoding/base64.spl:45`) and its first statement is
   `val bytes = data.bytes()` (`base64.spl:47`). `pem_encode` passed a `list`
   of i64, so `.bytes()` was invoked on an `array` — the reported error. The
   receiver in the message (`[0, 1, ... 31]`) is the spec's own DER fixture,
   which is why it looked like a spec problem.
2. `base_encoding.utilities` **never exported `line_wrap`/`line_unwrap` at
   all** — it provides only `bytes_to_text`, `text_to_bytes`,
   `validated_utf8_bytes_to_text_linear`, `text_to_bytes_linear`. Those two
   imports were dangling (`[use-warning]` on every load).

## Resolution

Base64 and line wrapping are now implemented locally over `[u8]` inside
`src/os/crypto/pem.spl` (`_b64_encode_bytes`, `_b64_value`,
`_b64_decode_to_bytes`, `_line_wrap`, `_line_unwrap`); the dead
`_u8_to_list`/`_list_to_u8` bridges are deleted. The fix stays inside
`src/os/crypto/**` and touches no shared encoder.

Routing the body through `text` would have been wrong even once it compiled:
PEM bodies are arbitrary binary, and any DER byte >= 0x80 becomes a multi-byte
UTF-8 sequence, so the bytes coming back out are not the ones that went in.
The codec therefore stays in byte space end to end.

| | `pem_rfc7468_kat_spec.spl` |
|---|---|
| before | `error: semantic: method 'bytes' not found on type 'array'` — file did not load, **0 examples ran** |
| after | `executed=13 passed=13 failed=0` |

Class-detection spec:
`test/01_unit/os/crypto/pem_binary_roundtrip_class_spec.spl` (7/7). The KAT
fixture is 32 bytes valued 0..31 — all below 0x80 — so it would pass against a
text-routing implementation too. The class spec round-trips all 256 byte
values and the 0x80..0xFF half exactly, checks the body is really RFC 4648
base64 (`0xFB 0xFF 0xFE` → `+//+`, 1-byte body → `AA==`) rather than merely
self-consistent, and checks 64-column wrapping. It carries a guard example
asserting the high-byte fixture really contains bytes >= 0x80.

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
