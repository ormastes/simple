---
id: aarch64_lowering_emit_aesimc_x86_symbol_collision_2026-05-03
status: RESOLVED
severity: high
discovered: 2026-05-03
discovered_by: AArch64 cipher lowering golden byte test (lowering_aarch64_crypto_spec.spl)
related: src/compiler/70.backend/lowering/intrinsic_lowering_aarch64.spl
related: src/compiler/70.backend/backend/native/encode_aarch64_crypto.spl
related: src/compiler/70.backend/backend/native/encode_x86_64_crypto.spl
related: src/compiler/70.backend/backend/native/__init__.spl
---

# AArch64 `crypto_aes_inv_round` calls x86 `emit_aesimc` due to symbol collision

**Status:** RESOLVED 2026-05-09. Option A fix (rename to `emit_aesimc_aarch64` /
`emit_aesmc_aarch64`) already landed. All 24/24 lowering_aarch64_crypto_spec tests
PASS in interpreter mode including the previously-failing `crypto_aes_inv_round`.
**md5:** `5ce0feeef43118e03996e086b01c8d96` (`encode_aarch64_crypto.spl`)

## Summary

`lower_cipher_intrinsic_aarch64("crypto_aes_inv_round", ...)` produces the
wrong bytes at runtime. Instead of emitting the AArch64 `AESIMC` encoding
(`0x4E287800 | (Rn<<5) | Rd`), the interpreter calls the x86 `emit_aesimc`
and produces the x86 opcode prefix `66 0F 38 DB`.

Golden test discovered this: expected `4158284e2178284e`, got `4158284e660f38db`.

## Root Cause

Both `encode_aarch64_crypto.spl` and `encode_x86_64_crypto.spl` define a
function named `emit_aesimc`. Both are re-exported by
`src/compiler/70.backend/backend/native/__init__.spl`:

```
# __init__.spl line:
export emit_aese, emit_aesd, emit_aesmc, emit_aesimc   # from encode_aarch64_crypto
# (encode_x86_64_crypto also exports emit_aesimc via intrinsic_lowering_x86 imports)
```

`intrinsic_lowering_aarch64.spl` uses an explicit named import:

```
use compiler.backend.backend.native.encode_aarch64_crypto.{
    emit_aese, emit_aesd, emit_aesmc, emit_aesimc, ...
}
```

Despite the explicit per-module `use`, the interpreter resolves the call to
the x86 `emit_aesimc` (likely via `intrinsic_lowering_x86` which is imported
for `LoweringResult`, and whose transitive imports shadow the local binding).

## Why Only `emit_aesimc` Is Affected

`emit_aesmc` exists only in `encode_aarch64_crypto.spl` — no x86 collision.
Therefore `crypto_aes_round` (AESE+AESMC) passes while
`crypto_aes_inv_round` (AESD+AESIMC) fails.

All other AArch64 intrinsics (SHA-256, CRC32, PMULL) use functions with
unique names not present in the x86 module, so they are unaffected.

## Confirmed by Test

`test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl`:

```
it "AESD+AESIMC V1,V2 (crypto_aes_inv_round [1,2]) — full decrypt round (8 bytes)":
    expect(_list_hex(result.bytes)).to_equal("4158284e2178284e")
    # actual: "4158284e660f38db" — second 4 bytes are x86 AESIMC opcode
```

23 of 24 tests pass; this one exposes the cross-arch symbol collision.

## Impact

Any AES decrypt operation lowered for AArch64 will emit x86 bytecode
instead of ARM bytecode, producing an immediate illegal instruction fault
on AArch64 targets. AES encrypt is unaffected.

## Proposed Fix Options

A. **Rename `emit_aesimc` in one module.** Rename the AArch64 variant to
   `emit_aesimc_aarch64` (or the x86 variant to `emit_aesimc_x86`) to
   eliminate the collision. Update all callers (lowering + tests).
   Safest fix, no interpreter behavior change needed.

B. **Fix interpreter symbol resolution to respect explicit per-module `use`.**
   The root cause is that the Rust seed interpreter allows transitive imports
   to shadow an explicit named `use`. Fixing this is the correct language
   semantic, but requires Rust-seed work and may affect other symbol resolution
   paths.

C. **Move `LoweringResult` import away from `intrinsic_lowering_x86`.**
   The x86 collision path enters via the `use intrinsic_lowering_x86.{LoweringResult}`
   import. If `LoweringResult` is moved to a shared module (e.g.
   `compiler.backend.lowering.types`), the x86 module need not be imported
   at all, breaking the collision chain.

## Recommended Fix

Option A is the immediate fix (pure-Simple rename, no Rust-seed work).
Option B should follow as a correctness fix for the interpreter.

## Files to Edit (for Option A)

- `src/compiler/70.backend/backend/native/encode_aarch64_crypto.spl:64`
  — rename `fn emit_aesimc` → `fn emit_aesimc_aarch64`
- `src/compiler/70.backend/backend/native/__init__.spl`
  — update re-export name
- `src/compiler/70.backend/lowering/intrinsic_lowering_aarch64.spl:20,117`
  — update import + call site
- `test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl`
  — update golden bytes once fix is in (expected: `4158284e2178284e`)

## Citations

- `src/compiler/70.backend/backend/native/encode_aarch64_crypto.spl:64` (AArch64 `emit_aesimc`)
- `src/compiler/70.backend/backend/native/encode_x86_64_crypto.spl:114` (x86 `emit_aesimc`)
- `src/compiler/70.backend/backend/native/__init__.spl` (re-exports both)
- `src/compiler/70.backend/lowering/intrinsic_lowering_aarch64.spl:18-20` (explicit import, silently overridden)
- `test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl` (failing test)
