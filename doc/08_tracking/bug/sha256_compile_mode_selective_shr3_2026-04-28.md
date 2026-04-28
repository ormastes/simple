# Bug: pure-Simple SHA-256 in compile mode selectively right-shifts 5 of 32 output bytes by 3

**Date:** 2026-04-28
**Severity:** correctness — silently corrupts SHA output in baremetal Cranelift builds
**Discovered by:** TLS live-lane bisection (`/dev tls_live_bug_fix_restart`, round 2)

## Symptom

For `sha256("")` in compile-mode (Cranelift bare-metal `x86_64-unknown-none`):

```
got    : 227 22  196 66  19  252 28  20  154 251 244 25  153 111 185 36  39 174 65 228 100 155 147 76 164 149 153 27 15 82 23 85
expected: 227 176 196 66  152 252 28  20  154 251 244 200 153 111 185 36  39 174 65 228 100 155 147 76 164 149 153 27 120 82 184 85
```

5 wrong bytes at positions 1, 4, 11, 28, 30. **Each wrong byte equals the correct byte right-shifted by 3:**
`0xb0>>3=0x16, 0x98>>3=0x13, 0xc8>>3=0x19, 0x78>>3=0x0f, 0xb8>>3=0x17`.

`sha256("abc")`, HMAC-TC1, and HKDF-Expand all show downstream corruption with the same root cause.

## Reproduction

In a baremetal compile-mode kernel build, call pure-Simple `os.crypto.sha256.sha256(b"")` and compare the 32-byte output to RFC 6234's empty-string vector.

Pure-Simple SHA-256 source: `src/os/crypto/sha256.spl` (algorithmically correct per FIPS 180-4).

## Root cause hypothesis (not confirmed)

A miscompilation that selectively applies an extra `>> 3` at certain points inside the SHA round mixing. Function-parameter narrow is fine (verified with `_bisect_shift_probe` showing `inline (h[0] >> 3)` and `helper_fn(h[0])` produce identical bytes). The `var`-rotation in the round loop is fine (rewriting with fresh `val`s changed nothing). The R1 `MirInst::UnitNarrow` patch landed in `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:361-370` (and two more sites) — fires on U32 array reads, but did not change the wrong-byte pattern.

Most likely sources: an interaction between Cranelift `sshr`/`ushr` selection and the SHA schedule recurrence; or an artifact in how `_u32_mask(...)` chains are codegened.

## Workaround in tree (2026-04-28)

`sha256_with_len()` in `src/os/crypto/sha256.spl` delegates to the C extern `rt_tls13_sha256` (in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`), which uses a known-good C SHA-256 implementation. All HMAC/HKDF callers route through this path. The pure-Simple implementation is preserved as `_sha256_pure_simple_with_len` for hosted-mode fallback and as the algorithm-of-record.

## Why root-cause fix matters

Workaround is acceptable for x86_64 baremetal but doesn't generalize to other targets that won't ship the TLS C externs. Any pure-Simple cryptographic primitive that uses `[u32]` heavy bitwise mixing in compile-mode is at risk of the same selective miscompile.

## Investigation pointers

Bisection tools left in tree under `examples/simple_os/arch/x86_64/tls_unit_entry.spl` (`_bisect_pure_simple_sha_hmac()`, B-SHA empty/abc/HMAC-TC1 prints). Diagnostic scaffolding can be reactivated by re-enabling pure-Simple `sha256_with_len`.

Memory note: `feedback_cranelift_shr_bug.md` (FR-DRIVER-0002b, 2026-04-18) fixed an earlier `>>` bug. This is a separate, narrower selective-`>> 3` issue.
