---
id: simd_aesni_runtime_stub_only_2026-05-02
status: OPEN
severity: medium
discovered: 2026-05-02
discovered_by: K1 (Wave K AES SIMD wire-up agent — stalled mid-test)
related: doc/01_research/cipher_simd_patterns_2026-05-02.md (J2)
related: doc/08_tracking/bug/bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md (K2)
---

# AES-NI / Vec16u8 round-op externs are stub declarations only

## Summary

`src/lib/nogc_sync_mut/simd.spl:521-522` declares:

```
extern fn rt_simd_aes_round_u8x16(state: Vec16u8, key: Vec16u8) -> Vec16u8
extern fn rt_simd_aes_round_last_u8x16(state: Vec16u8, key: Vec16u8) -> Vec16u8
```

But the comment block at lines 445-447 explicitly states:

> This is the Phase 2 SEED — type carrier + add op only. simd_aes_round /
> simd_xor_u8x16 / simd_shuffle_u8x16 / PCLMUL are deferred to follow-up
> waves (they require AES-NI exposure / different intrinsics).

J2's audit (`doc/01_research/cipher_simd_patterns_2026-05-02.md`) read the
extern declarations as wired and concluded "TRIVIAL ~50 LOC wire-up".
That conclusion was wrong: there is no runtime backing for these externs
yet. K1 (Wave K AES wire-up agent) stalled mid-test because the dispatch
would have failed at runtime.

## Required infrastructure (NOT yet present)

1. AES-NI runtime impl in `src/runtime/` for x86 (uses `_mm_aesenc_si128`)
2. ARMv8 Crypto Extensions runtime impl for ARM (uses `vaeseq_u8` + `vaesmcq_u8`)
3. Capability detection: x86 CPUID bit 25 of ECX (AES) for AES-NI; ARM
   AArch64 ID_AA64ISAR0_EL1.AES for ARMv8 Crypto Extensions
4. Runtime registration in `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs`
   (Cranelift calling convention) and `src/compiler_rust/compiler/src/interpreter_extern/ffi_array.rs`
   (interpreter dispatch) — same Rust-seed registration K2 found is required
5. Fallback scalar implementation for hosts without AES instructions
6. Fix J2's audit doc to mark these as "stub-only / deferred" rather than
   "wired"

## Why same blocker as K2

K2 (zstd bulk-copy SIMD) found that adding new SIMD-bearing externs requires
edits to the Rust seed (Cranelift FFI table + interpreter dispatch table),
not just `src/runtime/` C/Rust code. That blocker also applies here: even
once an AES-NI runtime is written in `src/runtime/`, registering it as
callable from `.spl` requires Rust-seed work the user has explicitly
deferred.

## Workarounds (none give the SIMD speedup)

- **Pure-scalar AES** (current `cipher.spl` path): correct and tested but
  no speedup
- **Byte-by-byte Vec16u8 with table-lookup SubBytes**: encodes the AES
  round in pure Simple but loses the AES-NI hardware acceleration entirely
  — defeats the purpose; not faster than current scalar
- **No workaround unblocks the J2 "AES wire-up" recommendation without
  Rust-seed work**

## Proposed Fix Options

A. **Defer until Rust-seed unblocker lands.** AES-NI runtime + Rust-seed
   FFI registration is a single coherent ~1-day task; bundle it with the
   K2 zstd-bulk-copy infrastructure and any other Vec16u8 op the AES-NI
   wave needs.

B. **Document the stub-vs-real gap in `simd.spl` more loudly.** Add a
   compile-time or runtime check that errors with "AES-NI runtime not
   wired — see bug doc <ID>" so future agents do not waste a budget cycle
   on this.

C. **Update J2 doc** to recategorize "AES wire-up" from TRIVIAL to MEDIUM
   (requires Rust-seed work) — same recategorization applies to ChaCha20
   only if more than the existing 4 Vec4i extern paths are needed; K5
   confirmed the ChaCha20 path stays TRIVIAL because all required Vec4i
   ops are wired.

## Action items

- [ ] Decide A vs B (or both)
- [ ] If A: schedule the Rust-seed unblocker wave (parallel-claude budget
      permitting)
- [ ] If B: file a follow-up to add the runtime stub error message
- [ ] Update J2 doc with the recategorization regardless

## Citations

- `src/lib/nogc_sync_mut/simd.spl:445-447` (deferred-comment block)
- `src/lib/nogc_sync_mut/simd.spl:521-522` (stub extern declarations)
- `doc/01_research/cipher_simd_patterns_2026-05-02.md` §AES (J2 misread)
- `doc/08_tracking/bug/bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md` (K2 same blocker class)
