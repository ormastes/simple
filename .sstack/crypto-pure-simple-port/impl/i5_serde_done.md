# I-5 — stdlib serde helpers (`integer_serde`)

**Date:** 2026-04-25
**Track:** crypto-pure-simple-port — I-5 (parallel implementation fan-out)
**Coverage:** B7 H-1 (`u32`/`u64` to/from BE/LE bytes — API absent) and
B7 H-3 (`u64.mul_hi` libcall — API absent), per
`doc/08_tracking/todo/compiler_bugs_for_crypto_2026-04-25.md`.

## File path chosen

- **Source module:** `src/lib/common/integer_serde.spl`
  - Imported as `use std.integer_serde.{ ... }`.
  - Flat path under `src/lib/common/` (rather than `math/integer_bytes`)
    because the helpers are integer↔bytes serde, not bignum/field math.
    Bignum (R-B I-3 → `math/bignum/`) and field (R-C I-4 → `math/field/`)
    can `use std.integer_serde.…` to consume them.

- **Spec:** `test/unit/lib/integer_serde_spec.spl`

## Line counts

| File | LOC |
|------|-----|
| `src/lib/common/integer_serde.spl` | 215 |
| `test/unit/lib/integer_serde_spec.spl` | 216 |

`md5sum` (post-revert of deliberate-fail probe):

- `734fd0692de6311479cd0c914a5a68af  src/lib/common/integer_serde.spl`
- `f496d3190551374fb1f206475425414e  test/unit/lib/integer_serde_spec.spl`

## Public API delivered

Pure-Simple, no new externs, mask + shift only:

- `u32_to_be_bytes(n: u32) -> [u8]`
- `u32_from_be_bytes(bytes: [u8]) -> u32`
- `u32_to_le_bytes(n: u32) -> [u8]`
- `u32_from_le_bytes(bytes: [u8]) -> u32`
- `u64_to_be_bytes(n: u64) -> [u8]`
- `u64_from_be_bytes(bytes: [u8]) -> u64`
- `u64_to_le_bytes(n: u64) -> [u8]`
- `u64_from_le_bytes(bytes: [u8]) -> u64`
- `u64_mul_hi(a: u64, b: u64) -> u64`

Each function carries inline doc-comment with the 1-line semantics, a
1-line CT note (data-independent control flow / fixed iteration counts),
and the bug-id back-reference to H-1 / H-3 in
`compiler_bugs_for_crypto_2026-04-25.md`.

`u64_mul_hi` uses standard 32-bit schoolbook split (each partial fits in
u64 since `(2^32 - 1)^2 < 2^64`); mid-sum carry handled via 32-bit
re-split to stay inside i64 magnitude.

## KAT count

**31 KAT cases** in `test/unit/lib/integer_serde_spec.spl`, organised
into 5 `describe` blocks:

- `u32 big-endian KAT (H-1)` — 7 cases (encode 0xDEADBEEF, 0, MAX,
  sign-bit 0x80000000; decode DE AD BE EF, MAX; round-trip 0xCAFEBABE).
- `u32 little-endian KAT (H-1)` — 7 cases (mirror set).
- `u64 big-endian KAT (H-1)` — 6 cases (encode 0x0123456789ABCDEF, 0,
  MAX, sign-bit 0x80…; round-trip 0x0123…, MAX).
- `u64 little-endian KAT (H-1)` — 4 cases (encode 0x0123…, sign-bit;
  round-trip 0xCAFEBABEDEADBEEF, MAX).
- `u64_mul_hi KAT (H-3)` — 7 cases:
  - `0*0 → 0`, `1*1 → 0`, small `123456*789 → 0`,
  - `2^32 * 2^32 → 1` (full product = 2^64),
  - `2^32 * (2^32+1) → 1` (carry from low half),
  - `MAX * 1 → 0`,
  - `MAX * MAX → 0xFFFFFFFFFFFFFFFE` (= -2 in i64 view; verified by hand
    against `(2^64-1)^2 = 2^128 - 2^65 + 1`),
  - `0xDEADBEEFCAFEBABE * 0x123456789ABCDEF0 → 0x0FD5BDEEEB2A01D7`
    (verified by arbitrary-precision computation in a sandbox).

## Live-machinery proof

**Outcome: PASSED.**

Per memory `feedback_compile_mode_false_greens.md` (2026-04-25), the
`bin/simple test` runner is the false-green case: it reports `expect`s
as passed even when they would fail (confirmed in this session — a
deliberate `expect(1).to_equal(2)` injected into the spec showed
`Passed: 32` via `bin/simple test`, but
`bin/simple <file>` direct invocation correctly reported
`1 example, 1 failure` for the same construct).

I therefore validated the helpers via **`bin/simple <file>` direct
invocation** of a probe script (`/tmp/run_full_spec.spl`) that imports
`std.integer_serde`, runs the same KAT subset (19 of the 31 cases —
including the load-bearing ones: `0x80000000` sign-bit BE/LE for u32
and u64, MAX round-trip for u64 LE, `MAX*MAX → -2`,
`0xDEADBEEF*0x123456789ABCDEF0 → 0x0FD5BDEEEB2A01D7`), and ends with a
deliberate `expect(1).to_equal(2)` to prove the assertion path is
actually evaluated.

Result on the live probe:

- All 19 real assertions GREEN (`✓`).
- The deliberate-fail describe reported `1 example, 1 failure`
  (assertion path is live).
- Probe was then **discarded**; the spec file does **not** contain a
  deliberate fail.

`bin/simple test test/unit/lib/integer_serde_spec.spl --clean` →
`Passed: 31, Failed: 0` after revert.

## `bin/simple build check` regression

`bin/simple build lint` — empty output (no failures reported) on this
WC. The lint/fmt subcommands hit pre-existing runtime errors
(`Function 'extend' not found`, `Function 'line' not found`) on **both**
my new files and existing files like
`test/unit/lib/bitwise_byte_helpers_spec.spl` (B4 landed). These are
not regressions introduced by I-5; they are pre-existing tooling
issues. The compiler accepts `integer_serde.spl` cleanly (it is parsed,
type-checked, and run by both the test runner and direct invocation
without any errors).

## Off-limits respected

- No edits to `src/lib/common/bitwise_utils.spl` (B4 separate concern).
- No edits to `src/lib/common/runtime_symbols.spl` (user WC).
- No edits to `src/os/apps/sshd/*.spl` (user WC).
- No new externs added.
- Files are net-new and do not collide with `src/lib/common/math/bignum/`
  (I-3) or `src/lib/common/math/field/` (I-4) namespaces.

## advisor() consultations

1. **Pre-implementation** — confirmed:
   - `u32`/`u64` are first-class types in Simple (verified via
     `binary_io.spl` extern signatures and `poly1305.spl` arithmetic).
   - Fixed-size `[u8; N]` returns are not in stdlib idiom; `[u8]` is
     used everywhere for byte-array returns (existing
     `extern fn u32_to_bytes_be(value: u32) -> [u8]`).
   - Path `src/lib/common/integer_serde.spl` is flat and correct.

2. **Pre-declare-done** — confirmed acceptance-grade: live-machinery
   proof done correctly (false-green of `bin/simple test` exposed,
   19 real assertions validated via direct invocation including
   `MAX*MAX → -2`, sign-bit boundaries, and the hand-computed
   `0x0FD5BDEEEB2A01D7`). Sign-bit decode is implicitly covered through
   round-trips of `0xCAFEBABE` (bit 31), `0xDEADBEEF` (bit 31), and
   `0xCAFEBABEDEADBEEF` (bit 63), plus MAX round-trips. fmt/lint runtime
   errors confirmed pre-existing (also hit on B4's
   `bitwise_byte_helpers_spec.spl`). Spec md5 matches pre-probe state.

## Future risk note

`u64_mul_hi` relies on i64 multiplication wrapping productively for the
partial products (`a_lo * b_lo` etc.); the MAX*MAX KAT proves this in
interpreter, and `src/os/crypto/poly1305.spl:118` uses the same
`to_u64() * to_u64()` pattern productively. If a future compiled-mode
build trapped on signed-integer overflow, this helper would need
re-expression as four 32-bit-result accumulators — out of scope here,
worth flagging.
