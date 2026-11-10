# Global SFFI ratchets drift and expose unhardened families
## Open 2026-11-11 — LIVE, both guards still fail (lane ne10; see addendum)

- **Status:** OPEN — re-confirmed LIVE 2026-11-11 lane ne10: both guard commands still fail
- **Filed:** 2026-08-26
- **Area:** SFFI admission and unsafe-surface tooling
- **Severity:** critical — global safety gates are not green

## Evidence

`scripts/check/check-raw-sffi-unsafe-ratchet.shs` reports 11,356 `rt_`
declarations: 2,826 tagged, 8,281 untouched, and 0 signed-admitted. Its baseline
comparison fails with 540 new and 3,435 stale entries. Regenerating the baseline
would silently grandfather new unsafe declarations and is not an acceptable
fix.

`scripts/audit/sffi-null-signature-guard.shs` independently fails. Checked
dynload/symbol providers and typed boolean thunks have since removed those WFFI
findings, but stale TCP/UDP ABI expectations, runtime null contracts, and missing
checked crypto bindings remain.

## Unblock condition

Review the 540 new declarations by provider family: remove duplicates, add
minimal lexical unsafe contracts where raw access is required, or replace
fabricated-value APIs with checked status/out contracts. Remove only genuinely
stale baseline rows. Implement signed exact-artifact admission, then require
both commands to pass without broad exclusions or baseline regeneration.

---

## 2026-11-11 addendum — lane ne10 (P3 traverse, batch ne10)

**Verdict: LIVE — keep OPEN.** Both guard commands were re-run on this tree; both still fail, in
the same families named above.

- **`scripts/check/check-raw-sffi-unsafe-ratchet.shs` → exit 2.** The contract inventory itself
  fails before baseline comparison:
  `SFFI contract inventory: FAIL source_variants=402/399 migration=3876/3546` — both over their
  ratchet ceilings. Measured now: total=14,854 declarations (was 11,356 at filing),
  unsafe_tagged=4,305, **signed_admitted=0** (unchanged), untouched=8,640. Debt grew past the
  tightened thresholds; the drift direction is still adverse.
- **`scripts/audit/sffi-null-signature-guard.shs` → exit 1.** Failing findings include the exact
  families this record names: stale TCP/UDP ABI expectations (`rt_io_udp_recv_from` raw `[u8]`
  declarations/calls in `src/lib`, `test/05_perf/bench/http_server/bench_udp_echo.spl`,
  `test/01_unit/compiler/mir/optional_tuple_byte_array_slot_spec.spl`) and missing checked
  crypto bindings (`ecdsa_p256_sign_fixed` in `src/os/crypto/ecdsa_p256.spl`,
  `cose_sign1_create` in `src/os/crypto/cose.spl`, plus sshd/jwt call-site lints).
- **Unblock condition status:** not met. Signed exact-artifact admission is still absent
  (signed_admitted=0 everywhere), and neither command passes without exclusions or a baseline
  regeneration. The required provider-family review/hardening work is a large audit lane, out of
  scope for P3 traverse.
