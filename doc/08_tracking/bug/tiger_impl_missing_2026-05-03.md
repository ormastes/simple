# Bug: Tiger Hash Implementation Never Landed (W20-F Precondition Missing)

**Date:** 2026-05-03
**Reported by:** W29-R (KAT verification run)
**File:** `src/os/crypto/tiger.spl` — ABSENT
**Spec:** `test/unit/os/crypto/tiger_kat_spec.spl` — ABSENT
**Reference:** Anderson & Biham, "Tiger: A Fast New Hash Function" (1996)

---

## Symptom

Task W29-R was assigned to verify Tiger KAT spec coverage against canonical
Anderson/Biham vectors (Tiger(""), Tiger("abc"), Tiger("Tiger"), 56-byte
boundary, 1MB-'a' @slow). The task prerequisite states "Tiger impl already
exists per W20-F".

Neither the implementation nor the test file exists:

- `src/os/crypto/tiger.spl` — not found
- `src/os/crypto/tiger*.spl` — no match
- `test/unit/os/crypto/tiger_kat_spec.spl` — not found

A full search confirms no Tiger symbol anywhere in `src/`:
```
grep -rn 'tiger' src/ --include='*.spl'  -> (no output)
```

Git history for the path is empty:
```
git log --all --oneline -- src/os/crypto/tiger.spl  -> (no output)
```

`src/lib/common/crypto/legacy_hash.spl` contains only MD5, not Tiger.

---

## Impact

W29-R is blocked. No KAT spec can be written against a non-existent module —
a `use os.crypto.tiger.{...}` import would be unresolvable and tests would
produce false-green load-only results (see
`.claude/memory/feedback_compile_mode_false_greens.md`).

**vectors_passed: 0/5 (impl missing)**

---

## Root Cause

W20-F either:
1. Was never executed, or
2. Produced a commit that was dropped/reverted before reaching current `main`

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
