# Correction: todo_db P1 `interpreter` rows describe a defect that no longer reproduces

**Date:** 2026-08-18
**Rows:** 6, 40, 96, 155, 355, 418, 487 (`doc/08_tracking/todo/todo_db.sdn`)
**Verdict:** premise stale — all seven rows amended to `done, false`.

## What the rows claimed

> Simple wraps SFFI `[u8]` returns as `Option::Some([bytes])` at the call-site
> binding even when the wrapper return type says plain `[u8]` ... Repro: 17
> failing tests in `test/03_system/os_crypto_ref_signature_spec.spl` with
> `method len not found on type enum (receiver value: Option::Some(...))`.

## Why there are seven rows, not seven defects

All seven carry byte-identical text and line number 129. They differ only in
path: `src/lib/...`, `src/std/...`, and five mirrored copies under
`test/01_unit/`, `test/unit/`, `test/feature/`. They are duplicate scanner hits
of **one** TODO comment in `src/lib/nogc_sync_mut/io/signature_sffi.spl`.

That comment no longer exists — `grep -n TODO
src/lib/nogc_sync_mut/io/signature_sffi.spl` returns nothing.

## Evidence the defect is gone (both engines)

The named repro path no longer exists; the spec moved to
`test/03_system/os/os_crypto_ref_signature_spec.spl`. It is fully green — the
claimed 17 failures are 0:

```
Results: 39 total, 39 passed, 0 failed
```

A regression pin for this exact defect already exists and is green:

```
SPEC FILE VERDICT: test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0
Results: 4 total, 4 passed, 0 failed
```

Cranelift JIT (`bin/simple run`) on a minimal fixture calling
`rsa_sha256_sign` / `ed25519_sign_pkcs8` / `ecdsa_p256_sign` and taking
`.len()` on each result:

```
rsa len=0
ed25519 len=0
ecdsa len=0
```

No `Option::Some` wrapping, no `method len not found`, on either engine.

## What is still broken (filed separately)

Sweeping siblings of the class did surface two live defects — an interpreter
`nil` binding for a declared `-> [u8]` extern, and a cross-engine
`rt_bytes_alloc(...).len()` disagreement. See
`sffi_u8_return_nil_and_cross_engine_len_2026-08-18.md`. Those are **not** the
defect these rows describe.
