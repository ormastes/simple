# M-B — `crypto-pure-simple-port` Curve25519 backend cleanup (done)

Wave 2.  Date: 2026-04-25.  Author: M-B (Sonnet sub-agent).

## Summary

Deleted the three obsolete Curve25519 backends. Trimmed the survivor's now-dead
import + 6 re-export shims. Marked the survivor `@deprecated` pending the
wave-3 curve-layer port. **Did not** repoint `x25519`/`x25519_base` callers —
the target curve-layer module (`src/lib/common/math/curve/`) does not exist
yet, so a repoint would be malformed.

## Caller sweep (before → after)

See `m_b_caller_sweep.md` for the full table. Counts of imports of each
obsolete module:

| Module | Before | After |
|---|---|---|
| `os.crypto.curve25519_bigint` | 2 (curve25519.spl, curve25519_bigint_wrapper.spl) | **0** (both removed) |
| `os.crypto.curve25519_bigint_wrapper` | 0 | **0** |
| `os.crypto.curve25519_smalllimb` | 0 | **0** |
| `os.crypto.curve25519` (survivor) | 8 importers | 8 (unchanged — wave 3) |

External-caller count for each obsolete was 0 before and after. They were
reachable only from each other; deletion was safe.

## Files deleted

- `src/os/crypto/curve25519_bigint.spl` (517 LOC)
- `src/os/crypto/curve25519_bigint_wrapper.spl` (26 LOC)
- `src/os/crypto/curve25519_smalllimb.spl` (531 LOC)

Total purged: 1074 LOC of obsolete-by-evidence backend (workarounds for
`feedback_cranelift_shr_bug.md` (closed FR-DRIVER-0002b 2026-04-18) and B2
`[u8]` quadratic (closed `e4b572b7c4`)).

## Files modified

`src/os/crypto/curve25519.spl` — survivor, 1291 → 1288 LOC.
md5 final: `c9807785dfd94f880daa71ef27625425`. Changes:

1. Added `@deprecated` doc block (lines 4–15) pointing at
   `src/lib/common/math/field/fe25519.spl` for field ops and at the wave-3
   curve-layer port for the X25519 driver.
2. Removed `use os.crypto.curve25519_bigint.{x25519_safe, x25519_base_safe,
   bigint_roundtrip_probe, bigint_mask_probe, bigint_cswap_probe,
   bigint_ladder_probe}` (former line 14).
3. Removed 6 dead re-export shims (former lines 643–659):
   `x25519_bigint_probe`, `x25519_base_bigint_probe`,
   `x25519_bigint_roundtrip_probe`, `x25519_bigint_mask_probe`,
   `x25519_bigint_cswap_probe`, `x25519_bigint_ladder_probe`. They forwarded
   into the now-deleted backend; keeping them would have been a compile error.
4. Replaced 1.–3. with a 4-line removal-marker comment.

## Tests run

| Spec | Method | Result |
|---|---|---|
| `test/system/os_crypto_ref_primitives_spec.spl` | `bin/simple <spec>` direct | **31/31 green** (12 ChaCha20 + 8 Poly1305 + 8 ChaCha20-Poly1305 + **3 X25519 RFC 7748**) |
| `test/system/os_crypto_spec.spl` | `bin/simple <spec>` direct | rc=0 (baremetal entry, no sspec output) |
| `bin/simple lint src/os/crypto/` | dir lint | **clean** ("lint: src/os/crypto/ OK") |

## Deliberate-fail probe (per `feedback_compile_mode_false_greens.md`)

**First attempt (failed false-green check):** flipped
`clamped[31] = clamped[31] | 0x40` → `0x20` in the **first** `_clamp_scalar`
(line 636). Tests still green — discovered the survivor file has TWO
`_clamp_scalar` functions (the `#![allow(unnamed_duplicate_typed_args)]` at
line 1 is for exactly this dupe). The first copy is dead code; the live one
that `x25519_smalllimb` calls is at line 1204. Reverted, md5 matched baseline
`c9807785dfd94f880daa71ef27625425`.

**Second attempt (succeeded):** flipped the line-1214 clamp `| 0x40 → | 0x20`.
All 3 X25519 RFC 7748 tests went **red** (`✗`) as expected. Reverted; md5
matched baseline `c9807785dfd94f880daa71ef27625425`. Re-ran tests: all 3
green again. Probe is real, not a false-green.

(Side note for follow-up: the orphan first `_clamp_scalar` at line 621 is
itself a deletion candidate — only `x25519_fe_probe` (line 712) calls it, and
the probe will be retired with the wave-3 curve-layer port. Out of scope here;
flagged in the `m_b_caller_sweep.md` holdouts section indirectly.)

## Holdout (intentional)

`src/os/crypto/curve25519.spl` itself is **not** deleted in this wave per the
M-B brief: "Don't delete src/os/crypto/curve25519.spl in this track — that's a
separate motion once all consumers are routed through fe25519.spl." 8 callers
(`os/crypto/mod.spl`, `os/tls13/tls13.spl`, `os/apps/sshd/ssh_kex.spl`,
`os/crypto/ed25519.spl`, two `test/system/os_crypto*spec.spl`, plus internal
references) need the `x25519`/`x25519_base` driver. fe25519.spl (I-4 frozen)
exposes only field ops, no curve layer.

**No bridge module added**: per advisor guidance, a `pub use` from
`os.crypto.curve25519 → fe25519` would be a partial alias (fe25519 has no
x25519/x25519_base). Defer cleanly to wave-3 curve-layer port.

## advisor() points + handling

Called once before any deletion (orientation already done):

> "Your analysis is correct. The repoint task is structurally blocked, but the
> deletion path is clean."

Followed all four pieces of advice:
1. Deleted the 3 obsoletes (not blocked by any external caller — verified via grep).
2. Removed the line-14 import + 6 re-export shims in curve25519.spl.
3. Did NOT touch the in-file `x25519_smalllimb` body — it's the survivor scalar-mult body, separate motion in wave 3.
4. Added `@deprecated` doc + wave-3 TODO.
5. Did NOT add a fe25519 bridge re-export (fe25519 has no x25519 — would be a footgun).

Probe-after-flip discovered the dual `_clamp_scalar` definitions; first probe
landed on the dead copy. This is the kind of false-green the memory note
warns about; a second probe at the live call site flipped 3/3 X25519 vectors
red, confirming the test path is real.

## Acceptance gates (all green)

- [x] `git status` shows the 3 obsoletes deleted (`D` in status).
- [x] `test/system/os_crypto_ref_primitives_spec.spl` X25519 RFC 7748 KAT 3/3 green.
- [x] Deliberate-fail probe flips one path red, then reverts (md5 verified
      `c9807785dfd94f880daa71ef27625425` matches pre-flip).
- [x] Directory-scoped lint `bin/simple lint src/os/crypto/` clean.
- [x] No new compile errors elsewhere (grep finds 0 stale refs to
      `curve25519_bigint`/`curve25519_smalllimb`/`x25519_safe`/`bigint_*_probe`
      outside the documentation comment in `curve25519.spl:656`).

## Wave-3 follow-ups (NOT done here)

- Port `x25519`, `x25519_base`, `_clamp_scalar`, `_mask_u_coord`, `_cswap_pair`,
  `_ladder_step`, and the in-file `x25519_smalllimb`/`_x25519_fe_*` scaffold
  to `src/lib/common/math/curve/{montgomery,curve25519}.spl` per R-C
  `field_design.md` §2/§5.
- Repoint the 8 callers, then delete `src/os/crypto/curve25519.spl`.
- Retire the `x25519_fe_probe` / `x25519_base_fe_probe` scaffolding lines
  714–784 (and the orphan first `_clamp_scalar` at line 621) at the same time.
