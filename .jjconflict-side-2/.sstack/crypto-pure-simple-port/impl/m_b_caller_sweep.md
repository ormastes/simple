# M-B caller sweep — `crypto-pure-simple-port` wave 2

Date: 2026-04-25.  Scope: repoint Curve25519 callers at the new pure-Simple
field module `src/lib/common/math/field/fe25519.spl` (landed by I-4) and delete
the three obsolete backends.

## 1. Imports of the four `os.crypto.curve25519*` modules

| Importer | Symbols imported | Lives in M-B scope? |
|---|---|---|
| `src/os/apps/sshd/ssh_kex.spl:21` | `x25519, x25519_base` | NO — user WC, frozen |
| `src/os/crypto/mod.spl:19` | `x25519, x25519_base` | YES |
| `src/os/crypto/curve25519.spl:14` | `x25519_safe, x25519_base_safe, bigint_roundtrip_probe, bigint_mask_probe, bigint_cswap_probe, bigint_ladder_probe` (all from `curve25519_bigint`) | YES (this is the file being trimmed) |
| `src/os/crypto/ed25519.spl:16` | `Fe25519, fe_zero, fe_one, fe_add, fe_sub, fe_mul, fe_sq, fe_invert, fe_reduce, fe_from_bytes, fe_to_bytes` | NO — M-C scope |
| `src/os/crypto/curve25519_bigint_wrapper.spl:1` | full bigint surface (re-export) | YES (file being deleted) |
| `src/os/tls13/tls13.spl:31` | `x25519` | YES |
| `test/system/os_crypto_spec.spl:13` | `x25519, x25519_base` | YES |
| `test/system/os_crypto_ref_primitives_spec.spl:40` | `x25519, x25519_base` | YES |

Counts of imports of each obsolete module (post-mortem of "is it reachable from
outside the obsoletes themselves?"):

| Module | External imports | Internal-only imports |
|---|---|---|
| `os.crypto.curve25519_bigint`         | **0**  | 2 (`curve25519.spl:14`, `curve25519_bigint_wrapper.spl:1`) |
| `os.crypto.curve25519_bigint_wrapper` | **0**  | 0 |
| `os.crypto.curve25519_smalllimb`      | **0**  | 0 |

All three obsoletes are reachable only from files this track owns (or are about
to delete). They are deletable.

## 2. Why `x25519` callers cannot be repointed in this wave

`fe25519.spl` (I-4, lines 1–576) exports field operations only:
`fe_zero/one/add/sub/neg/mul/sq/reduce/from_bytes/to_bytes/invert/inv/pow/eq/is_zero/cond_select/cond_swap`
and the `Fe25519` struct.

It does NOT export `x25519`, `x25519_base`, the Montgomery ladder
(`_ladder_step`), or `_clamp_scalar`. Per R-C's `field_design.md` §2 + §5, the
curve-level layer (`Montgomery` / `x25519` driver) lives in
`src/lib/common/math/curve/{montgomery,curve25519}.spl` — that tree does **not
exist yet** and is a wave-3 deliverable, out of scope for M-B (wave 2).

Therefore I cannot move `ssh_kex.spl`, `os/crypto/mod.spl`, `os/tls13/tls13.spl`,
`os_crypto_spec.spl`, or `os_crypto_ref_primitives_spec.spl` off
`os.crypto.curve25519` in this wave. Doing so would force an alias/bridge for a
function that doesn't exist on the target side.

`ed25519.spl` could *in principle* be repointed at `os.lib.common.math.field.fe25519`
for the field operations, but `ed25519.spl` is explicitly M-C turf in the M-B
scope brief — left untouched.

## 3. Decisions

- **Do not** repoint any caller in this wave. (No bridge module either: a
  partial alias to `fe25519` would be a footgun for the wave-3 curve port.)
- **Do** delete the three obsoletes (zero external callers, see §1 table).
- **Do** trim the now-dead `os.crypto.curve25519_bigint.*` import + 6
  re-exports inside `curve25519.spl` (lines 14, 643–660 — they would be a
  compile error after `curve25519_bigint.spl` is deleted).
- **Do** mark `src/os/crypto/curve25519.spl` `@deprecated` with a TODO pointing
  at the wave-3 `src/lib/common/math/curve/` port. Do not delete the survivor
  in this wave per the M-B brief.
- **Do not** touch `src/os/crypto/ed25519.spl` (M-C), `src/os/apps/sshd/*.spl`
  (user WC), `src/lib/common/math/field/**` (I-4), `src/os/crypto/rsa*.spl`
  (M-A), `src/os/crypto/ecdsa_p256.spl` (M-D pending).

## 4. Acceptance for this wave (deletion-only)

- `grep -rn 'x25519_safe\|x25519_base_safe\|bigint_(roundtrip\|mask\|cswap\|ladder)_probe' src test` → 0 hits post-edit.
- `grep -rn 'curve25519_bigint\|curve25519_smalllimb' src test` → 0 hits post-edit (the documentation reference inside `bignum/mod.spl:14` is a doc comment about migration history, kept).
- `test/system/os_crypto_spec.spl` and `test/system/os_crypto_ref_primitives_spec.spl` green via `bin/simple <spec>` direct invocation; deliberate-fail probe in `curve25519.spl::_clamp_scalar` flips one to red, then reverts (md5 verified).

## 5. Holdouts blocking `os/crypto/curve25519.spl` deletion

Will be resolved in wave 3 (curve-layer port to `src/lib/common/math/curve/`):
- 8 importers of `os.crypto.curve25519` (table §1).
- The in-file `x25519_smalllimb` / `x25519_base_smalllimb` ladder body (~660
  LOC, lines 1172–1291 + helpers) and `x25519_fe_probe` body (lines 714–784).
  These are the wave-3 source for the `curve/montgomery.spl` port.
