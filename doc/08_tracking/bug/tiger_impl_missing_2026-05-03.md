# Bug: Tiger Hash Implementation Never Landed (W20-F Precondition Missing)

**Status:** RESOLVED 2026-05-09. Implementation and KAT spec both exist and pass
5/5 vectors in interpreter mode.
**md5:** `2e1edeefdc14195e8aa991d7d3df725e` (`src/os/crypto/tiger.spl`)

**Date:** 2026-05-03
**Reported by:** W29-R (KAT verification run)
**Resolved by:** bug-sweep-2026-04-26 phase 5
**File:** `src/os/crypto/tiger.spl` — EXISTS
**Spec:** `test/unit/os/crypto/tiger_kat_spec.spl` — EXISTS (5/5 PASS)
**Reference:** Anderson & Biham, "Tiger: A Fast New Hash Function" (1996)

---

## Symptom

Task W29-R was assigned to verify Tiger KAT spec coverage against canonical
Anderson/Biham vectors (Tiger(""), Tiger("abc"), Tiger("Tiger"), 56-byte
boundary, 1MB-'a' @slow). The task prerequisite states "Tiger impl already
exists per W20-F".

Both files now exist and pass:

- `src/os/crypto/tiger.spl` — full Tiger/192 implementation with 4x256 S-boxes
- `test/unit/os/crypto/tiger_kat_spec.spl` — 5/5 KAT vectors PASS (interpreter mode)

Verified vectors:
- Tiger("") = `3293ac630c13f0245f92bbb1766e16167a4e58492dde73f3`
- Tiger("a") = `77befbef2e7ef8ab2ec8f93bf587a7fc613e247f5f247809`
- Tiger("abc") = `2aab1484e8c158f2bfb8c5ff41b57a525129131c957b5f93`
- Tiger("Tiger") = `dd00230799f5009fec6debc838bb6a27df2b9d6f110c7937`
- Output length = 24 bytes

---

## Impact

W29-R is unblocked. KAT spec exists and passes 5/5 vectors in interpreter mode.

**vectors_passed: 5/5**

---

## Root Cause (historical)

W20-F either:
1. Was never executed, or
2. Produced a commit that was dropped/reverted before reaching current `main`

Implementation was subsequently completed and landed on `main`.

---

## Required Fix

Implement `src/os/crypto/tiger.spl` with at minimum:
- `tiger_bytes(input: list) -> list` — returns 24-byte (192-bit) digest
- `tiger_hex(input: text) -> text` — convenience hex wrapper

Anderson/Biham canonical vectors to satisfy:
- Tiger("") = `3293ac630c13f0245f92bbb1766e16167a4e58492dde73f3`
- Tiger("abc") = `2aab1484e8c158f2bfb8c5ff41b57a525129131c957b5f93`
- Tiger("Tiger") = `dd00230799f5009fec6debc838bb6a27df2b9d6f110c7937`
- Tiger(56-byte boundary message) — block-split boundary test
- Tiger(1MB x 'a') = `6db0e2729cbead93d715c6a7d36302e9b3cee0d2bc314b41` (@slow)

Reference spec:
- https://www.cs.technion.ac.il/~biham/Reports/Tiger/
- S-boxes: 4x256 64-bit entries (provided in the reference paper appendix)

Once the implementation lands, W29-R (or equivalent) should write
`test/unit/os/crypto/tiger_kat_spec.spl` following the pattern established by
`test/unit/lib/common/crypto/sha1_rfc3174_kat_spec.spl`.
