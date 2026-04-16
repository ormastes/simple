# Crypto Test-Spec Remaining Failures — 2026-04-16

**Generated:** 2026-04-16
**Context:** After landing the signing-FFI work + 4 polish-wave commits + the cross-check test specs, two specific failures remain. This doc captures everything a future debugger needs to pick them up cold.

## Snapshot

| Spec | Pass | Fail | Notes |
|------|-----:|-----:|-------|
| `test/system/os_crypto_spec.spl` | 1 | 0 | ✓ no regression |
| `test/unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` | 22 | 0 | ✓ all 4 host-key algos pass |
| `test/system/os_crypto_ref_primitives_spec.spl` | 26 | **1** | poly1305 RFC 7539 §2.5.2 byte[0] |
| `test/system/os_crypto_ref_signature_spec.spl` | 22 | **17** | Simple interp Option<[u8]> wrapping |

Run with:
```
cd /home/ormastes/dev/pub/simple
export LD_LIBRARY_PATH=$PWD/src/compiler_rust/target/release:$LD_LIBRARY_PATH
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple test <spec>
```

---

## Issue #1 — `poly1305_finalize` produces wrong tag byte[0]

**File:** `src/os/crypto/poly1305.spl`
**Failing test:** `test/system/os_crypto_ref_primitives_spec.spl:227` "Poly1305 RFC 7539 §2.5.2: MAC byte[0] == 0xa8"
**Inline TODO comment:** `src/os/crypto/poly1305.spl:159` (poly1305_finalize docstring)

### Symptom

For the canonical RFC 7539 §2.5.2 vector:
- key (hex): `85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b`
- msg: `"Cryptographic Forum Research Group"` (34 bytes)
- expected tag: `a8 06 1d c1 30 51 36 c6 c2 2b 8b af 0c 01 27 a9`
- **actual tag:**  `ae 06 1d c1 ...` (only byte[0] differs; rest matches)

byte[0] differs by exactly +6 (0xa8 vs 0xae; XOR = 0x06 = bits 1+2).

### Reference confirmation

Python `cryptography.hazmat.primitives.poly1305.Poly1305` produces `a8061dc1305136c6c22b8baf0c0127a9` on the same input — confirming the RFC vector and the expected output.

### What is NOT the bug (eliminated by inspection)

1. **r-clamp constants** — verified byte-for-byte against poly1305-donna 32-bit reference:
   - `r0 & 0x3FFFFFF`, `r1 & 0x3FFFF03`, `r2 & 0x3FFC0FF`, `r3 & 0x3F03FFF`, `r4 & 0x00FFFFF`
2. **Convolution chain** in `poly1305_block` (lines 118-122):
   - `d0 = h0*r0 + h1*s4 + h2*s3 + h3*s2 + h4*s1` (and similar for d1..d4)
   - Verified against ∑h_i·r_j·2^((i+j)·26) modulo (2^130-5) reduction
3. **Carry propagation in `poly1305_finalize`** — canonical h1→h2→h3→h4→h0·5→h1 sequence (h0 already <2^26 entering finalize, so initial h0 carry is a no-op)
4. **Mask-select** `(g4 >> 31) - 1` — straightforward u32 logic

### Likely cause

The +6 in h0's low byte after a single 34-byte message points to one of:

- **`poly1305_block` overflow** in the `h0 += c * 5` step (line 143) — but c is bounded ~2^28, c*5 ~2^30, fits u32
- **Limb load step** for the partial block (`75 70 01 00 ...`) — but t0 = 0x00017075 verified
- **Subtle operator-precedence or type-promotion quirk** in the Simple interpreter (e.g., `~mask` doing i64 complement instead of u32)
- **`_le_u32` byte-order error** at a specific offset (eliminated for offsets 0, 12 by computation)

### Recommended debug approach

1. Add `eprintln!` (Rust runtime side) or `print` (Simple) for `h0 .. h4` after each `poly1305_block` call and after `poly1305_finalize` carry steps.
2. Compute reference intermediate h state via Python:
   ```python
   # Mock poly1305-donna in Python with print at each step
   ```
3. Diff Simple's intermediate values against reference to find first divergence.
4. Look especially at the `~mask` complement at line 207 — Simple may sign-extend.

### Acceptance test

Once fixed, `test/system/os_crypto_ref_primitives_spec.spl` should report 27/27 passing.

---

## Issue #2 — Simple interpreter `Option<[u8]>` wraps FFI sign returns

**File:** `src/lib/nogc_sync_mut/io/signature_ffi.spl` (workaround), but root cause is in `src/compiler_rust/compiler/src/interpreter_extern/`
**Failing tests:** 17 of 39 in `test/system/os_crypto_ref_signature_spec.spl`
**Inline TODO comment:** `src/lib/nogc_sync_mut/io/signature_ffi.spl:107` (`_unwrap_sig` docstring)

### Symptom

A test like:
```
val sig = rsa_sha256_sign(pkcs8, msg)
expect(sig.len() > 0).to_equal(true)
```
fails with:
```
semantic: method `len` not found on type `enum`
(receiver value: Option::Some([101, 43, 134, 40, ...]))
```

The Rust interpreter handler `rt_rsa_sha256_sign` returns `Value::Array(...)`. The Simple wrapper `rsa_sha256_sign(...) -> [u8]` calls `_unwrap_sig(rt_rsa_sha256_sign(...))` which pattern-matches Option to plain `[u8]`. Yet the caller still sees `Option::Some([bytes])` at the binding site.

### Workaround attempts (all unsuccessful)

| Attempt | Outcome |
|---------|---------|
| `_unwrap_sig` shim in `signature_ffi.spl` | `signature_ffi.{rsa_sha256_sign,...}` body returns `[u8]` correctly internally, but Simple type inference at the call site still sees `Option<[u8]>` |
| `_rsa_unwrap` / `_ecdsa_unwrap` mirror in `src/os/crypto/rsa.spl` and `src/os/crypto/ecdsa_p256.spl` | Same — wrapper-side unwrap doesn't propagate to caller |
| Test-spec local `_sign_rsa256(...) -> [u8]` with internal `if val sig = ... else: []` | Same |
| Inline `if val sig = _sign_rsa256(...): ... else: ...` in each `it` block | Same — `var` declarations inside the matched branch report as undefined later |
| `var bad_sig: [u8] = []` BEFORE the `if val` (outer-scope) | Still `bad_sig not found` (suggests scope visibility through `if val` is broken) |

### Failing tests (categorized)

**Byte-exact `Simple sign == openssl sign` (6 — 3 each for rsa-256 + rsa-512):**
- `sign Hello World: Simple == openssl (byte-exact)` ×2
- `sign empty message: Simple == openssl (byte-exact)` ×2
- `sign 1 KB: Simple == openssl (byte-exact)` ×2

**Round-trip + tampered (6 — 3 each for rsa-256 + rsa-512):**
- `round-trip: Simple sign -> Simple verify -> true` ×2
- `negative: tampered signature -> Simple verify = false` ×2 — surfaces as `bad_sig not found`
- `large (4 KiB) message: sign + verify succeed` ×2

**ECDSA (4):**
- `sign then Simple verify -> true (sig1)`
- `second independent signature also verifies via Simple`
- `negative: flip bit in message -> Simple verify = false` — surfaces as `bad_msg not found`
- `empty message: ECDSA sign + Simple verify succeed`
- `large (4 KiB) message: ECDSA sign + Simple verify succeed`

(2 of these have explicit `bad_sig`/`bad_msg not found` errors which are downstream consequences of the Option issue stopping semantic analysis early.)

### Root cause hypotheses

1. **Multi-decl extern resolution**: `rt_file_read_bytes` exists with both `-> [u8]` (in `ffi/io.spl`) and `-> [u8]?` (in `fs.spl`). Simple's resolver may pick the Option-returning one for sign externs too — even when the canonical declaration in `signature_ffi.spl` says plain `[u8]`. Worth grepping for any duplicate `rt_rsa_sha256_sign` decls in alternate `.spl` files.

2. **Interpreter dispatch return type**: `src/compiler_rust/compiler/src/interpreter_extern/signatures.rs::rt_rsa_sha256_sign` returns `Value::Array(...)`. If Simple's type checker doesn't recognize that as a plain `[u8]` and conservatively wraps it as Option, every binding gets the wrap.

3. **`if val` scoping bug**: Variables declared inside an `if val` matched-branch don't propagate to the outer scope, AND outer-scope variables defined before the `if val` aren't visible inside it. This would explain both the receiver-Option issue (for the binding) AND the downstream `bad_sig not found` errors.

### Recommended debug approach

1. **Repro-minimize**: write a single-file Simple program that calls `rt_rsa_sha256_sign` directly (no wrappers) and calls `.len()` on the result. If it errors, the bug is in the interpreter dispatch / type inference. If it works, the bug is in wrapper layering.
2. **Trace Simple's type checker** for the `_sign_rsa256` wrapper — what type does it infer for the return? Should be `[u8]`; if it infers `Option<[u8]>`, the bug is in inference.
3. **Look at `interpreter_extern/dynamic_ffi.rs`** — its return marshalling forces all extern returns to `i64`. Maybe even with our static dispatch in `signatures.rs`, the type checker still consults dynamic_ffi's signature for the type hint.
4. **Add a `pub fn` rather than `fn`** for the wrapper — Simple may handle pub vs private differently for type propagation.

### Acceptance test

Once fixed, `test/system/os_crypto_ref_signature_spec.spl` should report 39/39 passing.

---

## Other minor cleanups noted but not blocking

- **`rt_ed25519_sign` KAT cross-check** — extern landed via concurrent commit `xk 47`; signature spec doesn't yet have an Ed25519 RFC 8032 KAT. Trivial to add once Issue #2 is resolved (need PKCS#8-wrapped Ed25519 fixture).
- **`testing.md` interpreter limitation note** — should document the dynamic_ffi i64 marshalling limitation so future test authors don't burn cycles on Option mysteries.

---

## Already-fixed during this session (for context, not action)

- ✓ `_hex_digit` `or`-precedence bug — split into individual `if` branches
- ✓ `extract_bytes` rejected bytes ≥128 (signed i64 wraparound) — switched to `*i as u8` truncation
- ✓ `RuntimeValue::NIL` vs empty-array contract for sign error path — added `_empty_bytes()` helper
- ✓ Push-loop array consumption in 3 primitives spec blocks (S3 fix) — replaced with inline literals
- ✓ S3 typos `rt_file_write` → `rt_file_write_bytes`, `openssl_ecdsa_p256_verify` → `_der`
- ✓ Interpreter dispatch handlers for 7 sign/verify externs in `interpreter_extern/signatures.rs`
- ✓ `if-val` restructure on RSA-256/512 tampered-sig blocks (cosmetic — needs Issue #2 fix to actually pass)
