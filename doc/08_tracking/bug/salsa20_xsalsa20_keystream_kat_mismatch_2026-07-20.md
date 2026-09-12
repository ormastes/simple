# Salsa20 / XSalsa20 keystream does not match DJB/NaCl/libsodium reference vectors

- **Date:** 2026-07-20
- **Area:** Salsa20/XSalsa20 implementation exercised via `test/unit/lib/crypto/salsa20_spec.spl` and `salsa20_kat_spec.spl`
- **Severity:** high (real cryptographic KAT mismatches — output is wrong,
  not merely mis-imported).
- **Status:** OPEN. **Do not touch the expected vectors** — they are the
  canonical DJB/NaCl/libsodium published values.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/salsa20_spec.spl --no-session-daemon
```

```
✗ block output matches DJB spec byte-exact
    expected 2aba3dc45b4947007b14c851cd694456b303ad59a465662803006705673d6c...
    to equal 317d791ffc3244d546d67610c5ed433513edd736097c4ae8632d86db9ed12c...

✗ output matches NaCl reference vector byte-exact
    expected dc908dda0b9344a953629b733820778880f3ceb421bb61b91cbd4c3e66256c...
    to equal 497effe5cd82a90db6582a8e272b1853ff287ebb56ed241cf72da5bc56248a5...

✗ encryption matches computed ciphertext byte-exact
    expected f47b8d74044e8ee43ed033d6f348b7f7b99f5e55c259906ac00a6c038d4ae26...
    to equal e2621942f7273a851cbb9f954eb75e78d5cd859e173d01efa870eefbc65a815...
```

3 distinct KAT mismatches across 3 describe blocks (14 examples total, 11
pass, 3 fail — the other 11 exercise round-trip/length properties that
don't depend on matching an external reference).

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/salsa20_kat_spec.spl --no-session-daemon
```

```
✗ XSalsa20 keystream first 32 bytes match libsodium test
    expected [238, 166, 167, 37, 28, 30, 114, 145, 109, 17, 194, 203, 33,
      77, 60, 37, 37, 57, 18, 29, 142, 35, 78, 101, 45, 101, 31, 164, 200,
      207, 248, 128]
    to equal [62, 241, 252, 174, 157, 104, 242, 162, 73, 120, 12, 195, 198,
      253, 181, 2, 49, 147, 121, 5, 161, 58, 90, 77, 152, 186, 145, 110,
      247, 63, 61, 29]
```
1 of 9 examples fails; the other 8 (round-trip, output-length properties)
pass.

## Root-cause hypothesis

Both the base Salsa20 block function and the XSalsa20 (HSalsa20-derived
subkey) keystream produce output that diverges from three independently
published reference sources (the original DJB spec vector, the NaCl
reference implementation vector, and the libsodium test vector). Since the
*shape* of the output is correct (right length, deterministic, round-trips
correctly with itself) but the *values* are wrong against external
references, this points at an arithmetic bug in the Salsa20 core
quarter-round / column-round sequence, or in HSalsa20 subkey derivation for
XSalsa20 specifically — not an obviously-localized single line without
deeper implementation-level debugging (out of scope for this triage pass).
The two spec files likely share this one root in the Salsa20 core.

## What NOT to do

Absolutely do not change any of the three expected byte arrays to match the
computed (wrong) output — these are externally-verifiable published test
vectors (DJB spec, NaCl, libsodium), not internal fixtures.

## Affected specs

- `test/unit/lib/crypto/salsa20_spec.spl` (3 of 14 examples)
- `test/unit/lib/crypto/salsa20_kat_spec.spl` (1 of 9 examples)

## Re-check 2026-09-12 — NOT an implementation defect; four expected vectors were fabricated

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` sha256 `3d120a6f`

```
SIMPLE_RUST_SEED_WARNING=0 bin/simple test test/unit/lib/crypto/salsa20_spec.spl --no-session-daemon
SIMPLE_RUST_SEED_WARNING=0 bin/simple test test/unit/lib/crypto/salsa20_kat_spec.spl --no-session-daemon
```

RED: salsa20_spec 14 examples, 11 passed, 3 failed; salsa20_kat_spec 10 examples,
9 passed, 1 failed.

An independent Salsa20/20 + HSalsa20 + XSalsa20 reference implementation, written
from the DJB spec, was used to arbitrate every disputed value. It reproduces the
two vectors these specs already passed, so it is calibrated against published data:

| case | reference | `src/os/crypto/salsa20.spl` | spec's literal |
|---|---|---|---|
| key=0, nonce=0 (published eSTREAM) | `9a97f65b9b4c721b…` | same | same (passed) |
| key=0x80.., nonce=0 (published) | `e3be8fdd8beca2e3…` | same | same (passed) |
| key=0, nonce=0x80.. | `2aba3dc45b494700…` | same | `317d791f…` |
| NaCl HSalsa20 core test | `dc908dda0b9344a9…` | same | `497effe5…` |
| XSalsa20 ciphertext (35 B) | `f47b8d74044e8ee4…` | same | `e2621942…` |
| XSalsa20 keystream[0..32] (NaCl `crypto_stream_xsalsa20`) | `eea6a7251c1e7291…` | same | `3ef1fcae…` |

The implementation matches the reference on **every** case. `317d791f…` matches no
key/nonce/counter combination that was searched, and `dc908dda…` / `eea6a725…` are
the canonical NaCl outputs — i.e. the record's instruction "do not touch the
expected vectors, they are the canonical published values" was itself wrong for
these four literals. The "key=0, nonce=0x80.." case is not a published vector at
all (no published set pairs a zero key with a nonzero nonce) and is now labelled
as derived rather than as "DJB spec Set 2 vector 0".

GREEN: salsa20_spec 14/14, salsa20_kat_spec 10/10, in both `test/unit/` and
`test/01_unit/`.

- Status: RESOLVED (2026-09-12) — commit "fix(crypto): replace fabricated Salsa20/XSalsa20 expected vectors with verified ones", specs test/unit/lib/crypto/salsa20_spec.spl and test/unit/lib/crypto/salsa20_kat_spec.spl
