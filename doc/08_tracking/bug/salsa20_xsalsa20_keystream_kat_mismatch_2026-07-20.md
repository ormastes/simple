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
