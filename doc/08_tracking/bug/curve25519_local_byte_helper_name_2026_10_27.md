# Curve25519 Small-Limb Local Byte Helper Name Mismatch

Status: source repair; pinned-P2 native compile/link PASS, RFC7748 native
runtime qualification FAIL. Canonical bug database registration: PENDING.

The frozen object-campaign baseline at
`D:/dev/simple-all-objects-phase2-20261027/build/object-campaign/objects/c718ec0c9fbc4f25bdfe45181b7c4bc9/0b00acf93dabebb88a3481f10844b2fe67acfad866ee225f1ba08e5c47e98dae/compiler.log`
fails HIR lowering for
`src/os/crypto/curve25519_smalllimb.spl`. It reports ten unresolved-name
diagnostics for `_u8_at`, including calls in `_load3` and `_load4` at lines
50/53 and byte reads in the scalar/coordinate paths around lines 528/543.

The module already had a local byte accessor declared as
`_u8_at_i(data: [u8], idx: i64) -> u8`, implemented by
`rt_bytes_u8_at(data, idx).to_u8()`. Its callers consistently use `_u8_at`.
The source repair renames only the helper declaration to `_u8_at`; its type,
runtime call, signed index, byte conversion, and all cryptographic operations
remain unchanged. This is a local declaration/call-site name mismatch, not a
cryptographic algorithm change or an owner-export change.

Existing production-path regression evidence is in
`test/system/os_crypto_ref_primitives_spec.spl`: the public `x25519_base` and
`x25519` paths assert RFC7748 Alice's public key, the Alice/Bob shared secret,
and the one-step iterative vector. A focused native entry fixture is staged at
`build/object-campaign/scratch/curve25519_local_byte_helper/main.spl`; it calls
the real `x25519_base` path and compares the resulting bytes with RFC7748's
published Alice public key.

The root's already-completed pinned-P2 native executable build of the focused
fixture exited 0; its compiler log is
`build/object-repair/curve-rfc7748/compiler.log`. The subsequent execution of
`build/object-repair/curve_rfc7748.exe` exited 1. Runtime output reported that
`rt_bytes_u8_at` rejected an invalid array handle before dereference
(`value_bits=0x000001cbe7b34130`), followed by a bounds panic for index 0 with
length 0. The C runtime declares this boundary as
`rt_bytes_u8_at(SplArray*, int64_t)`, and `curve25519_smalllimb.spl` calls it
through its typed `[u8]` helper. `x25519_base` dispatches directly to
`x25519_base_smalllimb`, which builds a 32-byte base-point array and enters the
ladder. The observed invalid handle is consistent with an array-value ABI or
ownership mismatch at the native boundary, but these artifacts do not identify
which caller/callee conversion produced it. Execution failed during byte
access; no RFC output was produced, so the vector did not pass and no
cryptographic correctness claim is made.

The focused fixture and existing RFC7748 runtime regressions are therefore
UNQUALIFIED. Do not rerun the unchanged binary as part of this diagnosis.
Canonical bug database registration remains pending; this Markdown record
does not substitute for database registration.
