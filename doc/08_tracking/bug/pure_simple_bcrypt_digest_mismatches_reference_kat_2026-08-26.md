# pure-Simple bcrypt digest mismatches reference KAT (2026-08-26)

## Symptom
`src/os/crypto/bcrypt.spl` `bcrypt_hash` produces structurally valid $2a$04$
modular crypt strings (correct length 60, correct header, correct salt
encoding, deterministic, verify round-trips) but the 31-char DIGEST portion
does not match a reference bcrypt implementation.

Evidence (test/01_unit/lib/crypto/bcrypt_kat_spec.spl, cost=4):

- password `""`, salt chars `ZjIzMjE0/RWPtJ3BDSWKWe` (raw bytes
  6e52b53a51b6053611bcbe4315460c62):
  - reference (python `bcrypt.hashpw`): `$2a$04$ZjIzMjE0/RWPtJ3BDSWKWeUFMwHcw6cn92N10aRp/DxgtUb/grddq`
  - pure-Simple:                                       `$2a$04$ZjIzMjE0/RWPtJ3BDSWKWeJyi3z7lPoC.NhM.dl9hTJIkpwi8458G`
- password `"password"`, same salt:
  - reference: `$2a$04$ZjIzMjE0/RWPtJ3BDSWKWeux5LZcYpIu9JVIFCSDNv2Sps1f/qZHW`
  - pure-Simple: `$2a$04$ZjIzMjE0/RWPtJ3BDSWKW.ZR9LPYb8QLj3g4FjhdBVPBGFXunwLdO` (with pw+NUL variant also differing)

Appending the $2a$ NUL terminator was also tried and does NOT close the gap,
so this is not the 2a/2b password-termination convention.

## History
The legacy spec carried these two KATs as `pending(...)` behind FR
`bcrypt_native_runtime_helpers_2026-05-02` with expected strings
(`...WehnhrR8e.0.S...` / `...W.4/16.rPt...`) that match NEITHER the reference
NOR the pure-Simple output — i.e. the commented "expected" values were
unverifiable. During sspec modernization (2026-08-26) the pendings were
replaced with byte-exact assertions against python-bcrypt ground truth; they
fail, so the spec is intentionally RED until the digest defect is fixed.

## Unblock condition
Fix the eksblowfish/Blowfish core in `src/os/crypto/bcrypt.spl` until the two
KAT scenarios in `test/01_unit/lib/crypto/bcrypt_kat_spec.spl` pass byte-exact
against the reference values above.
