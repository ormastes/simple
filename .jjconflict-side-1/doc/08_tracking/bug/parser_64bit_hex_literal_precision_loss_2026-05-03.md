# Parser: 64-bit hex literals lose precision (silent truncation)

**Status:** RESOLVED (already fixed). The lexer at `src/compiler_rust/parser/src/lexer/numbers.rs:57-64`
already special-cases `NumericSuffix::U64` with `u64::from_str_radix`, preserving the full 64-bit
pattern. Regression spec added at `test/unit/compiler/u64_hex_literal_precision_spec.spl`.
**Path:** `bug` track. Parser/lexer.

## Symptom

A hex literal that requires the full 64 bits to represent (i.e., bit 63 is set)
is silently truncated or sign-extended at parse time. The literal value at
runtime differs from the source.

Examples that should keep their bit pattern:

```spl
val SHA512_IV0: u64 = 0x6a09e667f3bcc908u64    # IV: u64, fine
val SHA384_IV5: u64 = 0xdb0c2e0d64f98fa7u64    # IV: u64, fine
val MAX_U64:    u64 = 0xFFFFFFFFFFFFFFFFu64    # ALL bits set
val MASK_HIGH:  u64 = 0x8000000000000000u64    # only top bit set
```

In current Simple, MAX_U64 / MASK_HIGH may parse as something else — e.g.
sign-extended to negative i64 then re-cast to u64 with wrong magnitude, or
truncated to 32 bits. The exact symptom depends on whether the literal is
explicitly suffixed `u64` and the surrounding type context.

## Where this hits in practice

- SHA-512 / SHA-384 round constants (K[80]) — table of 80 u64 values, half of
  which have bit 63 set. The W16-B-FIX SHA-384 KAT failure
  (`doc/08_tracking/bug/sha384_kat_failure_2026-05-02.md`) was caused by an
  ALMOST-identical issue (u64 right-shift sign-extension on fn parameters); it
  is plausible that the K-table itself is also affected for some constants.
- Whirlpool S-box outputs (64-bit per row).
- Curve448 / Ed448 limb constants for the prime `p = 2^448 - 2^224 - 1`.
- BCH/Reed-Solomon GF(2^k) for k >= 32.

## Reproduction (probe spec)

```spl
fn _u64_top_bit() -> u64:
    return 0x8000000000000000u64

fn _u64_max() -> u64:
    return 0xFFFFFFFFFFFFFFFFu64

# Expected:
# _u64_top_bit() == 9_223_372_036_854_775_808
# _u64_max()     == 18_446_744_073_709_551_615
# Reality (interpreter): may differ — capture both values via
# `eprintln!("{}", _u64_top_bit())`-equivalent in compile mode and via
# the it-block assert in interpreter mode.
```

## Root cause hypothesis

Three candidates, in order of likelihood:

1. **Lexer parses literal as i64**, applies suffix `u64` after sign-extension or
   truncation. If the literal is `0xFFFF...` (fits in i64 only as -1 via
   two's-complement reinterpretation), the lexer rejects or silently
   reinterprets.
2. **Lower path between AST and HIR/MIR** truncates u64-typed-constant to i64,
   then converts back losing high bit.
3. **Backend/codegen** applies signed integer promotion when emitting LLVM
   constants, breaking high-bit values.

Probable site: `src/compiler_rust/compiler/src/lex/...` (literal parsing) or
the AST→HIR const-folder.

## Workaround

Construct the constant arithmetically at runtime (cheap one-time init):

```spl
fn mask_high() -> u64:
    return 1u64.shl(63)
```

Or split into two i64 halves and OR:

```spl
val TOP: u64 = (0x80000000u64).shl(32) | 0u64  # 0x80000000_00000000
```

Both are uglier and error-prone; the right fix is in the lexer.

## Affected modules

Audit needed for u64 constants with bit 63 set:
- `src/os/crypto/sha512.spl`, `src/os/crypto/sha384.spl` — K-tables
- `src/os/crypto/whirlpool.spl` — S-box (W29-N in flight)
- `src/os/crypto/streebog.spl` — S-box + L-permutation matrix (W28-I /tmp backup)
- `src/os/crypto/ed448.spl`, `src/os/crypto/curve448.spl` — field constants
- Any future RSA/PSS/PKCS1 code with large M_max constants

## Verification after fix

Probe spec at `test/unit/compiler/u64_hex_literal_precision_spec.spl`:

- `0x8000000000000000u64` decimal == `9223372036854775808`
- `0xFFFFFFFFFFFFFFFFu64` decimal == `18446744073709551615`
- `0xCAFEBABEDEADBEEFu64` round-trip via to_hex/from_hex is byte-exact

Should pass in BOTH compile mode AND interpreter mode after fix.

## Cross-references

- `doc/08_tracking/bug/sha384_kat_failure_2026-05-02.md` (related u64 corruption)
- `doc/08_tracking/bug/u64_right_shift_fn_param_arithmetic_2026-05-02.md` (sibling
  u64 corruption, fn-param shift; this bug is the literal-parse counterpart)
- `feedback_simple_parser_strict_callsites.md`
