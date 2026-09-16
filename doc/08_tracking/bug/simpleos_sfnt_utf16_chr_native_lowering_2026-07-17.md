# SimpleOS SFNT UTF-16 name decoding cannot materialize characters natively

**Status:** Fix implemented; fresh pure bootstrap and QEMU evidence pending
**Date:** 2026-07-17
**Owner:** compiler / core-C text runtime

## Symptom

After the allocation-constant pure-Simple SHA fix, the x86_64 SimpleOS guest
reads and hashes all 1,708,408 pinned font bytes, then SFNT name validation
emits repeated `unresolved fn: i64.chr` warnings and rejects the font.

Retained evidence:

- `build/simpleos_wm_font_oracle_run4/serial.log`
- `build/simpleos_wm_font_oracle_run4/report.md`

## Reproduction

`test/01_unit/lib/common/encoding/sfnt_utf16be_native.spl` exercises ASCII and
non-BMP UTF-16BE names through the same pure-Simple decoder. The admitted
Stage2/core-C native binary builds, but exits 3 because the ASCII result is not
`Noto`. Direct `.chr()` is unresolved in the guest. Replacing it with
`rt_bytes_to_text` over either `[u8]` or `[i64]` also produced the wrong native
text, so both experiments were reverted.

## Required fix

Repair the canonical pure-Simple/core-C codepoint-to-text lowering or its
byte-array ABI once. Do not special-case Noto names, weaken SFNT manifest
validation, or substitute a host-only font parser.

## Implemented fix

- Pure MIR lowers unresolved zero-argument integer `chr` / `to_char` to the
  existing `text_dot_from_char_code(raw i64) -> tagged text` runtime ABI.
- Both pure LLVM paths declare that ABI; all three Rust LLVM call paths now use
  it instead of the ASCII-only `char_from_code` suffix.
- Hosted core-C, Rust, pure simple-core, and one shared freestanding provider
  validate Unicode scalar values and encode one through four UTF-8 bytes using
  the same raw runtime ABI on every SimpleOS target.
- Regression sources cover the compiler redirect, runtime registry/provider
  parity, all six SimpleOS target provider includes, and end-to-end SFNT
  decoding of `Noto` plus `中😀`.

Focused evidence: Rust ABI, Unicode runtime, SFFI registration, ELF resolver,
and RV32 LLVM declaration/call regressions pass. Freestanding C syntax passes
for all six SimpleOS targets, and high-capability ABI review passes. A probe
built with the pre-fix pure compiler still reproduces the expected `i64.chr`
failure. Three bounded attempts to produce a fresh pure
compiler did not converge: the old pure compiler first hit the known hyphenated
worktree init-symbol bug, then a hyphen-free mirror exceeded the bounded build
window, and the Rust seed emitted a runaway diagnostics flood and was stopped.
Per the bootstrap retry guard, no further bootstrap or QEMU attempt was made in
this session.

## Acceptance

- The native UTF-16BE probe exits 0 for `Noto` and `中😀`.
- Existing malformed-surrogate SFNT tests still reject invalid input.
- SimpleOS emits no unresolved `i64.chr` warning, registers the pinned font,
  and reaches the taskbar-clock pixel oracle.
