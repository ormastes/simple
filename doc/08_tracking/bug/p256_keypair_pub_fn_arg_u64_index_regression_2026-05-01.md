# Bug: P-256 keypair_pub fails semantic when [u8] argument crosses fn-return boundary

- **Date filed:** 2026-05-01
- **Status:** Open — Verified, NOT a guess (per `.claude/memory/feedback_bug_doc_fixes_are_guesses.md`)
- **Severity:** Blocks W5-A AC-7 P-256 ECDHE → handshake_secret AC-6 spec round-trip,
  blocks the existing `p256_named_group_spec.spl` (regression from 13/13 PASS to 11/13 fail),
  blocks `cert_verify_ecdsa_spec.spl`, blocks `hello_retry_request_spec.spl` (13/17 fail).

## Symptom

Calling `p256_keypair_pub(s)` (or any function that ultimately exercises
`_scalar_mul_affine`) with `s: [u8]` whose value originated from a function
return triggers:

```
semantic: cannot index array with type `u64`
```

Wider variant on string-typed call sites:

```
semantic: cannot index string with type `u64`
```

(seen in `cert_verify_ecdsa_spec.spl`).

## Reproduction

Verified at HEAD = `932016c330` (2026-05-01) — minimal probe:

```spl
use std.spipe.*
use os.crypto.ecdh_p256.{p256_keypair_pub}

fn _cs() -> [u8]:
    var s: [u8] = []
    var i: u64 = 0u64
    while i < 31u64:
        s.push(0x00u8)
        i = i + 1u64
    s.push(0x01u8)
    s

describe "probe":
    it "inline build PASSES":
        var s: [u8] = []
        var i: u64 = 0u64
        while i < 31u64:
            s.push(0x00u8)
            i = i + 1u64
        s.push(0x01u8)
        val out = p256_keypair_pub(s)        # OK
        expect(out.len().to_u64()).to_equal(65u64)

    it "fn-return FAILS at semantic":
        val s: [u8] = _cs()
        val out = p256_keypair_pub(s)         # semantic: cannot index array with type `u64`
        expect(out.len().to_u64()).to_equal(65u64)
```

`it "inline build PASSES"` PASSES; `it "fn-return FAILS at semantic"` FAILS at
the semantic stage (not runtime). Same `s` byte content, only difference is
the binding source: var-built inline vs fn-return then `val s: [u8] = _cs()`.

The `var out: [u8] = []; out = p256_keypair_pub(s)` discriminator does NOT
work around it — the failure is on the call site, not the result binding.

## Scope

Affects every spec that funnels a fn-return `[u8]` (or text/string) into
P-256 / ECDSA-P256 / TLS 1.3 codepaths. Verified-failing specs:

- `test/unit/os/tls13/p256_named_group_spec.spl` — 11/13 fail (was 13/13 PASS at parent `844a65b0ec`).
- `test/unit/os/tls13/cert_verify_ecdsa_spec.spl` — 8/8 fail (string variant).
- `test/unit/os/tls13/hello_retry_request_spec.spl` — 13/17 fail.
- `test/unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl` — AC-3/AC-4
  blocked indirectly by `rt_tls13_hkdf_extract_into` extern wiring (separate
  but related runtime drift); AC-1 + AC-2 = 5/5 PASS via inline-scalar
  workaround.

## Provisional root cause (NOT verified — author hypothesis)

The width-tagged `Value::UInt` interpreter rework (commits
`2ec2342969 fix(interp): u32/u8/u16/u64 wrap arithmetic via Value::UInt with width tag`
and follow-ups) likely changed how `u64` values flow through the semantic
type checker. The `71e50b532c doc(zstd): mark zstd.spl:324 stale +
cross-link UInt-dispatch regression` doc explicitly cross-links a
"UInt-dispatch regression" — same family.

Possibility 2: `5b1abf1ea6 fix(p256): constant-time scalar multiplication on
secret path` introduced `p256_point_cselect` whose `if p0.inf: 1u64 else:
0u64` colon-form was hand-rewritten to brace-form here in this session
(no help). The semantic error happens BEFORE `p256_point_cselect` is
exercised — the call is rejected at the function-boundary type-check.

These are hypotheses; no minimal one-line repair has been verified.

## Workaround (in-spec)

Build `[u8]` arguments inline within the `it` block instead of calling a
module-level fn that returns them. This is what `p256_ecdhe_handshake_secret_spec.spl`
does for AC-1/AC-2 (5/5 PASS). It does NOT weaken coverage — the round-trip
is identical — but it inflates the spec by ~50 lines.

## Required fix

- Diagnose whether the regression is in semantic checker (likely
  `Value::UInt` width-tag dispatch) or in `_scalar_mul_affine` /
  `p256_point_cselect`.
- Repair without weakening fn-arg type inference for `[u8]`/`text` types.
- Land `rt_tls13_hkdf_extract_into` runtime wiring so AC-3/AC-4 of
  `p256_ecdhe_handshake_secret_spec.spl` can be re-enabled.
- Bring back the existing `p256_named_group_spec.spl` 13/13 PASS,
  `cert_verify_ecdsa_spec.spl` 8/8 PASS, `hello_retry_request_spec.spl` 17/17 PASS.

## Cross-references

- `doc/08_tracking/crypto_recovery_status.md` — Wave 6 P-256 ECDHE landing notes.
- Commits: `2ec2342969`, `71e50b532c`, `5b1abf1ea6`.
- `.claude/memory/feedback_bug_doc_fixes_are_guesses.md` — applied: this
  bug doc tags the proposed root-cause as hypothesis, not fact.
