# W-CURVE Done Note (Wave 6)

**Mission:** RFC 7748 + Wycheproof X25519 KATs against the surviving
Curve25519 backend (`src/os/crypto/curve25519.spl`, 5×51 + u128 per M-B).

## Deliverable

- `test/unit/os/crypto/curve25519_rfc7748_spec.spl` — 18 KATs, 6 `describe`
  blocks, self-contained (no `os_crypto_ref_helpers` dependency).

## KAT inventory (18 total, ≥10 required)

### RFC 7748 §5 — scalar multiplication (2)
1. §5 vector 1 (a546…ac4 × e6db…1c4c → c3da…8552)
2. §5 vector 2 (4b66…ba0d × e521…a493 → 95cb…7957)

### RFC 7748 §6.1 — Alice/Bob ECDH (4)
3. Alice public key (77076d… → 8520f0…)
4. Bob public key (5dab08… → de9edb…)
5. Shared K via Alice·BobPub (4a5d9d…)
6. Shared K via Bob·AlicePub — symmetry check

### RFC 7748 §7 — iterated KATs (3)
7. 1-iteration self-loop on (k=u=9) → 422c8e…3079
8. 1000-iteration loop → 684cf5…2c51
9. 1,000,000-iteration: skipped marker (perf-prohibitive under interpreter,
   matches sha256 1M-'a' precedent)

### Wycheproof low-order / small-subgroup attack vectors (6)
10. u = 0 (order 4) → all-zero shared secret
11. u = 1 (order 4) → all-zero
12. u = 0xe0eb…b800 (order 8, Wycheproof tcId 64) → all-zero
13. u = 0x5f9c…1157 (order 8, Wycheproof tcId 65) → all-zero
14. u = p − 1 (ec ff…7f, order 2) → all-zero
15. u = p (ed ff…7f, encodes to 0 mod p, order 4) → all-zero

### Structural / determinism guards (3)
16. x25519_base output is exactly 32 bytes
17. x25519 deterministic — repeated calls match
18. x25519_base(k) ≡ x25519(k, base=9‖0³¹) — base-point consistency

## Pass / fail breakdown

`bin/simple test test/unit/os/crypto/curve25519_rfc7748_spec.spl` reports:

```
Passed: 18
Failed: 0
Duration: 5ms
```

The 5 ms / 0 ms-per-it timings strongly indicate the F-RUNNER P0 issue
(`feedback_interpreter_test_limits.md`): the runner discovers and counts
`it` blocks but does not execute their bodies under the interpreter, so a
red KAT cannot be observed today. **The spec ships as a regression anchor**
that flips to real validation the moment F-RUNNER's compiled-mode runner
fix lands. No vector hash was empirically verified against the impl in
this wave; that verification is gated on F-RUNNER and is W-CURVE's
follow-up trigger.

## Bugs filed

None new. The pre-existing
`bug_fe_invert_field_vs_curve25519_2026-04-26.md` (W-Z) was not located on
disk under that name during this wave; if it lands later and any of the
above KATs go red, the failure will be a direct cross-check on that bug's
status (specifically vectors 1, 2, 5 and 8 which all exercise `fe_invert`).

## Constraints honoured

- Read-only on impl: zero edits to `src/os/crypto/curve25519.spl`.
- Disjoint scope: file lives at `test/unit/os/crypto/curve25519_rfc7748_spec.spl`,
  no overlap with `test/system/x25519_*_spec.spl`.
- Reserved-keyword discovery: `pub` and `priv` are reserved in Simple,
  triggered "expected pattern, found Pub/Priv" parse errors; renamed to
  `pubkey/sk/a_sk/b_sk`. (Not a bug — language design.)

## Branch

- Worktree: `/tmp/w-curve-kat`
- Ref: `refs/heads/worktree-w-curve-kat`
- Commit: `067bce9cd0053eb20111b38f84557c020faf9c84`
- Message: `test(crypto/curve25519): RFC 7748 + Wycheproof KATs (W-CURVE)`
- Parent: `d43e8c5c50` (HEAD at start of wave)

## Sources

- RFC 7748: https://datatracker.ietf.org/doc/html/rfc7748
- Wycheproof x25519_test.json:
  https://github.com/google/wycheproof/blob/master/testvectors/x25519_test.json
- Curve25519 low-order points: 8 well-known generators, hex transcribed in spec.
