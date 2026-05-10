# P-1 — FeP256 arithmetic (done)

**Track:** P-1 — Solinas-reduction P-256 field, parallel-fan-out wave 2 of
sstack feature `crypto-pure-simple-port`.
**Date:** 2026-04-25 (P-1 partial) → 2026-04-26 (W-4 finish).
**Status:** landed (worktree `/tmp/w4-fep256-wt`, detached HEAD; commit
hash recorded after `git commit` — see `git log` of the worktree).

## Authorship split

| Phase | Author | Scope |
|-------|--------|-------|
| Skeleton (152 LOC, 0 ops) | I-4 | `fe_p256.spl` byte-edge ops + struct + Solinas `panic` stubs. |
| Arithmetic (152 → 593 LOC) | P-1 | Solinas D.2.3 reduction, schoolbook 8×8 mul, fe_add/fe_sub/fe_neg/fe_mul/fe_sq/fe_inv/fe_pow/fe_eq/fe_is_zero/fe_cond_select/fe_cond_swap. P-1 hit org Opus monthly limit mid-flight; left two surface-level failures + one buried algorithmic bug. |
| Triage + Solinas correctness fix + KATs | W-4 | three fixes (see "Bugs found and fixed"); 55-KAT spec; cleaned skeleton spec; this done doc. |

Final size: **595 LOC**, **0 panic call-sites** in
`src/lib/common/math/field/fe_p256.spl`.

## Per-op LOC + algorithm choice

| Op | LOC | Algorithm |
|----|-----|-----------|
| `_addc` / `_subb` | 28 | 32-bit-half carry primitives, branch-free, every `>> 32` masked with `& MASK32` (interpreter signed-shift workaround). |
| `_be_load_u64` / `_be_store_u64` | 18 | Big-endian byte ↔ u64, public-index loops. |
| `fe_zero` / `fe_one` | 6 | Trivial constants. |
| `fe_from_bytes` / `fe_to_bytes` | 22 | 32 BE bytes ↔ 4 LE u64 limbs; `fe_to_bytes` calls `_canonicalize` first. |
| `fe_cond_select` / `fe_cond_swap` | 24 | Mask-form `mask = -take_b`, mask routed through `rt_black_box` (B6, commit `d42cde3a0f`). |
| `fe_eq` / `fe_is_zero` | 24 | `_canonicalize` + XOR/OR-accumulate, accumulator routed through `rt_black_box`. `fe_is_zero` tests both `a == 0` AND `a == p` to avoid the `_canonicalize`-loop dependency. |
| `_sub_p_with_borrow` / `_add_p_unchecked` / `_canonicalize` | 22 | Branch-free 4-limb sub/add; `_canonicalize` uses one `fe_cond_select` (no loop). |
| `fe_add` / `fe_sub` / `fe_neg` | 30 | 4-limb add or sub, branch-free correction via `fe_cond_select`. |
| `_mul_to_c` | 56 | Schoolbook 8×8 product into 16 32-bit limbs in u64 (each `>> 32` masked). |
| `_solinas_reduce` | 200 | FIPS 186-4 D.2.3 Solinas reduction in i64 32-bit limbs; offset 4*p plus `r8_seed = 3` (the bit-256 spill of 4*p) folded back via `2^256 ≡ 2^224 - 2^192 - 2^96 + 1 mod p`. Three carry-propagation rounds, then 16 fixed conditional `_sub_p_with_borrow` corrections. |
| `fe_mul` / `fe_sq` | 8 | `_solinas_reduce(_mul_to_c(a, b))`; `fe_sq(a) = fe_mul(a, a)`. |
| `fe_pow` | 18 | Square-and-multiply-always over LE-byte exponent; every bit performs a square AND a multiply, then `fe_cond_select` picks. |
| `fe_inv` | 14 | Fermat: `fe_pow(a, p-2)` with `p-2` baked as 32 LE bytes. |

## Bugs found and fixed (vs. P-1 handoff)

P-1's handoff cited **two failures**. W-4 found **three** root causes; all
are now fixed in this commit.

### Bug 1 (cited): "fe_one expected 2 to equal 1"

**Root cause:** Interpreter `u64 >> 32` performs **arithmetic** (sign-
extending) shift; `0xffffffffffffffff >> 32` returns `0xffffffffffffffff`
instead of `0xffffffff`. P-1 documented this in
`doc/08_tracking/bug/bug_interpreter_u64_shr_arithmetic_2026-04-25.md`
and added `& MASK32` workarounds in `_mul_to_c` and `_solinas_reduce`
but **missed** `_addc` / `_subb`. The byte test
`expect(out[31]).to_equal(0x01)` fired with `out[31] = 2` because
`_subb(1, P_L0, 0)` mis-computed the borrow chain (b_hi = -1 instead of
0xffffffff), leading `_canonicalize` to take the `(a - p)` branch when
it should have taken `a`.

**Fix:** every `u64 >> 32` in `_addc`, `_subb`, and the high-half
extracts of `_mul_to_c` (`a_arr.push(a.l0 >> 32)` etc., `prod_hi`,
`carry_hi`, `sum_hi`, the carry propagation `(carry >> 32) + (sum >> 32)`)
is now wrapped as `(x >> 32) & MASK32`. The i64 shifts inside
`_solinas_reduce` (lines 438-526) are intentionally arithmetic — they
sign-extend across negative carry — and are left unchanged.

### Bug 2 (cited): "function expects 2 argument(s), but 3 were provided"

**Root cause:** `fe_p256_skeleton_spec.spl` used `it.skip "name": nil`
form. Simple's parser normalizes that into `it(skip, "name", body)` —
3 arguments to a 2-argument `fn it(name: text, block: fn())`. The
sspec module exposes `skip_it` (2-arg) and `skip` (2-arg with
reason text), but **not** an `it.skip` member. P-1 inherited the
malformed pattern from I-4's skeleton spec.

**Fix:** the skeleton spec's `it.skip` placeholders are removed
entirely. Every op they were placeholdering for now has a real
implementation, and the new `fe_p256_full_spec.spl` covers them
with real assertions. The skeleton spec is reduced to a 6-test
byte-edge smoke check + a comment pointing at `fe_p256_full_spec.spl`.

### Bug 3 (NOT cited — buried, found by W-4): `_solinas_reduce` offset overflow

**Root cause:** P-1's `_solinas_reduce` adds `4*p` as a constant offset
to the result of `T + 2*s1 + 2*s2 + s3 + s4 - s5 - s6 - s7 - s8` so the
8 i64 slots stay non-negative. The offsets `off0..off7` encode the low
256 bits of `4*p`, but **the bit-256 carry-out of value 3 is dropped**.
P-1 had no bug-doc for this; their algorithm just silently lost ~`3*p`
worth of value on every multiply. Surface symptom: `fe_mul(0,0)` → some
non-zero garbage near `4*p mod 2^256`; `fe_mul(p-1, 1)` → wrong; `fe_mul(2, 3)`
→ wrong. Hidden by the failing skeleton spec — fe_mul tests never ran.

**Fix:** introduce `val r8_seed: i64 = 3` — the dropped bit-256 carry-
out of the 4*p offset — and fold it through the existing
`2^256 ≡ 2^224 - 2^192 - 2^96 + 1 mod p` reduction step:
`var top: i64 = (r7 >> 32) + r8_seed`. The remainder of the carry chain
naturally propagates the +3 contributions to slots (0, +3), (3, -3),
(6, -3), (7, +3). After this 5-byte change all 55 KATs in
`fe_p256_full_spec.spl` pass.

## KAT count + green run

Located at `test/unit/lib/math/field/fe_p256_full_spec.spl` (420 LOC).

| Category | KATs |
|----------|-----:|
| Field axiom — additive identity | 5 |
| Field axiom — additive inverse | 5 |
| Field axiom — associativity (3 × add, 2 × mul) | 5 |
| Field axiom — distributivity | 3 |
| Edge cases (`0`, `1`, `p`, `p-1`) | 5 |
| Random fe_add | 5 |
| Random fe_sub | 5 |
| Random fe_mul | 5 |
| Random fe_sq | 5 |
| Random fe_inv | 5 |
| `fe_cond_select` / `fe_cond_swap` branch coverage | 4 |
| `fe_pow` exponent paths | 3 |
| **Total** | **55** |

Direct invocation:
```
$ /tmp/w4-fep256-wt/bin/simple test/unit/lib/math/field/fe_p256_full_spec.spl
… 55 examples, 0 failures (across 12 describe blocks)
```

Inputs are sourced from FIPS 186-4 D.1.2.3 (Gx, Gy), an arbitrary
3rd random in-range scalar (`d62fa3e5…b48d`), and hand-derived small-
integer values. Each input is cited inline.

## Deliberate-fail probe (per `.claude/rules/testing.md` direct-invocation rule)

```
md5(spec) before flip:  aaaac599e7d7263501c19b04a4d99317
flip "expect(...).to_equal(true)" → ".to_equal(false)" on
  describe "FeP256 axioms — additive identity" / it "fe_add(0, random_b) == random_b"
md5(spec) after flip:   d14b4135f1a6f2f734456c2e85f05b4e
run shows: ✗ fe_add(0, random_b) == random_b   expected true to equal false
revert
md5(spec) after revert: aaaac599e7d7263501c19b04a4d99317  (matches original)
re-run shows: 55 ✓ markers, 0 failures
```

Hash-stable revert + flipped-red proof.

## CT correctness checklist (R-C §4)

| Function | Branch-free | No secret index | No early return | Notes |
|----------|-------------|-----------------|-----------------|-------|
| `_addc` | Y | Y | Y | Pure 32-bit-half arith; no `if` |
| `_subb` | Y | Y | Y | Bias-trick avoids signed-underflow branch |
| `_be_store_u64` | Y | Y | Y | Bounds check is on a public offset |
| `fe_add` | Y | Y | Y | Mask-form `1-borrow` flowed through `fe_cond_select` |
| `fe_sub` | Y | Y | Y | Same shape as fe_add |
| `fe_neg` | Y | Y | Y | `fe_sub(zero, a)` |
| `fe_mul` | Y | Y | Y | Schoolbook 8×8 + `_solinas_reduce`; no data-dep branches |
| `fe_sq` | Y | Y | Y | Same shape as `fe_mul` |
| `fe_pow` | Y | Y | Y | Square-and-multiply-always over public-but-CT-safe exponent |
| `fe_inv` | Y | Y | Y | `fe_pow(a, p-2)` |
| `fe_eq` | Y | Y | Y | XOR-accumulate, accumulator through `rt_black_box` |
| `fe_is_zero` | Y | Y | Y | OR-accumulate against both `0` and `p`, `rt_black_box`-protected |
| `fe_cond_swap` | Y | Y | Y | Mask through `rt_black_box` |
| `fe_cond_select` | Y | Y | Y | Mask through `rt_black_box` |
| `fe_to_bytes` | Y | Y | Y | `_canonicalize` is branch-free; `_be_store_u64` indices are public |
| `_solinas_reduce` | Y | Y | Y | All loops have public bounds; final 16 sub-p corrections each go through `fe_cond_select` |

`r8_seed = 3` is a public compile-time constant; no `rt_black_box` is
needed.

**Verdict:** CT-clean. No data-dependent branches anywhere on the secret
path. Mask-form everywhere. `rt_black_box` placement matches R-C §4.

## Workarounds preserved for the open W-23 interpreter bugs

W-23's docs (filed by P-1) at:
* `doc/08_tracking/bug/bug_interpreter_u64_shr_arithmetic_2026-04-25.md`
* `doc/08_tracking/bug/bug_interpreter_struct_field_index_assign_2026-04-25.md`

Workarounds in **`fe_p256.spl`** that **must remain** until W-23 lands a
compiler fix:

1. **Every `u64 >> 32` is masked `& MASK32`.** Sites:
   * `_addc` lines 64–66, 68, 70.
   * `_subb` lines 78–80.
   * `_mul_to_c` lines 309, 311, 313, 315, 318, 320, 322, 324 (a/b high-
     half pushes), 341, 343, 346, 355 (prod_hi, carry_hi, sum_hi, carry-
     propagation).
   The i64 shifts inside `_solinas_reduce` are intentional sign-extending
   shifts and are NOT masked.
2. **No `<obj>.<field>[<i>] = …` mutations on FeP256 limbs.** All limb
   writes go through `FeP256(l0: …, l1: …, l2: …, l3: …)` constructors.
   This naturally falls out of the chosen 4-named-limb representation;
   no workaround scaffolding required.

Workarounds in **`fe_p256_full_spec.spl`** (KAT spec):
3. **Every loop with `var i = 0; while i < N: …; i = i + 1` lives in a
   helper `fn`.** The interpreter's "`var` mutations inside while-inside-it-
   block are dropped" limitation (per
   `feedback_interpreter_test_limits.md`) means raw `it`-block loops
   silently do not iterate, leading to false-greens. Helpers force a
   function-scope frame where mutations persist. Documented inline in
   the spec header.

When W-23 closes both bugs the audits to remove these workarounds are:
* Compile `fe_p256.spl` with all `& MASK32` post-shift masks dropped on
  the u64 path; rerun `fe_p256_full_spec.spl`. Should still pass; the
  masks become no-ops.
* Inline the `fe_p256_full_spec.spl` helpers into `it` blocks; rerun.
  Should still pass; the var-while quirk is gone.

## Skeleton spec rerun

```
$ /tmp/w4-fep256-wt/bin/simple test/unit/lib/math/field/fe_p256_skeleton_spec.spl
FeP256 — skeleton constants:    2 ✓
FeP256 — skeleton byte round-trip: 2 ✓
FeP256 — skeleton equality:     2 ✓
6 examples, 0 failures (no orphan it.skip; no semantic errors)
```

## Open follow-ups (not blockers)

* `fe25519_spec.spl` (I-4 turf, frozen for this track) **is failing on
  HEAD with `rt_text_to_bytes not found`** — pre-existing I-4 bug, not
  introduced by W-4. Fix is one line: add `extern fn rt_text_to_bytes(s: text) -> [u8]`
  near the top of the spec. Filed for a future I-4 follow-up.
* The skeleton spec's `var ok = true; while …: ok = false; …; expect(ok)…to_equal(true)`
  pattern remains in the two skeleton-constants tests. It is unreliable
  (the var-while-in-it-block bug means `ok` may not actually flip even
  when bytes are wrong) but it is **redundant** with the real
  `expect(out[31]).to_equal(0x01)` check that sits right next to it and
  caught the original "expected 2 to equal 1" bug. Documented inline.
* `_solinas_reduce` carry-propagation does THREE rounds + the explicit
  `r8_seed` fold. With the new bookkeeping, ONE carry round + the fold
  is mathematically sufficient. Trim deferred to a perf-tuning track.

## R-C §4 references

* FIPS 186-4 §D.2.3 — P-256 Solinas reduction (T + 2s1 + 2s2 + s3 + s4 - s5 - s6 - s7 - s8).
* BoringSSL `crypto/fipsmodule/ec/p256.c::ecp_nistz256_mod_inverse` — the addition-chain pattern (left for a perf-tuning follow-up; current `fe_inv` uses Fermat-via-`fe_pow`).
* H. Cohen, *A Course in Computational Algebraic Number Theory* §10.4.
