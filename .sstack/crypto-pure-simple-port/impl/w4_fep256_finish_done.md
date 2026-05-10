# W-4 — FeP256 finish (done)

**Track:** W-4 — finish P-1's `crypto-pure-simple-port` wave-3 FeP256 work
that hit the org Opus monthly limit mid-flight in wave 2.
**Date:** 2026-04-26.
**Status:** landed (worktree `/tmp/w4-fep256-wt`, detached HEAD; will be
committed onto a `worktree-w4-…` branch as the closing step).

## TL;DR

P-1 produced 593 LOC of `src/lib/common/math/field/fe_p256.spl` with
0 panic stubs and handed off two failures + an undocumented buried
algorithmic bug. W-4 triaged all three, wrote a 55-KAT spec, cleaned
the skeleton spec, and authored the missing `p1_fep256_done.md`
continuation.

| Mission deliverable | Status | Detail |
|---------------------|--------|--------|
| 1. Triage `fe_one` failure | ✓ | Missing `& MASK32` workaround in `_subb` / `_addc` (interpreter `>>` arith-shift bug). |
| 2. Triage call-mismatch | ✓ | `it.skip "name": nil` in skeleton spec — sspec lacks `it.skip`; parser normalizes to a 3-arg call to a 2-arg `it`. Removed all `it.skip` lines. |
| 3. ≥40 KATs in `fe_p256_full_spec.spl` | ✓ | **55 KATs**, all green, sourced from FIPS 186-4 + hand-derived edges + 3 in-range "random" inputs. |
| 4. Clean `fe_p256_skeleton_spec.spl` | ✓ | All `it.skip` removed; reduced to a 6-test byte-edge smoke check; comment points at full spec. |
| 5. Deliberate-fail probe + md5 | ✓ | md5 `aaaac599…` → flip → `d14b4135…` → revert → `aaaac599…`; flipped run shows red ✗; revert run shows 55 ✓. |
| 6. Write `p1_fep256_done.md` | ✓ | `.sstack/crypto-pure-simple-port/impl/p1_fep256_done.md` (this companion file). |
| 7. Write `w4_fep256_finish_done.md` | ✓ | This file. |

Acceptance bar:
* 0 panic calls in `fe_p256.spl` ✓
* ≥40 KATs green via direct invocation ✓ (55 green)
* Deliberate-fail probe flips red ✓
* `fe_p256_skeleton_spec.spl` rerun is clean (no orphan `it.skip`) ✓ (6/6 green)
* CT checklist signed off in `p1_fep256_done.md` ✓
* No regression in `fe25519_spec.spl` ✓ (it has a pre-existing
  `rt_text_to_bytes not found` failure that is **identical** before and
  after W-4's changes — fe25519 is I-4 turf, frozen, untouched by W-4)

## Two surface-failure fixes

### 1. `fe_one` encode broken — root cause + 1-line shape

**Root cause:** Interpreter sign-extends `u64 >> 32` when the source has
bit 63 set (filed as
`doc/08_tracking/bug/bug_interpreter_u64_shr_arithmetic_2026-04-25.md`).
P-1 added `& MASK32` masks in `_mul_to_c` and `_solinas_reduce` but
forgot `_addc` and `_subb`. The downstream effect: `_subb(1, P_L0, 0)`
mis-computed `b_hi = -1` instead of `0xffffffff`, producing borrow=0
when borrow=1 was correct, which made `_canonicalize(fe_one())` flip
into the `(a - p)` branch and return 2 in the low byte.

**Fix:** in `_addc` and `_subb`, every `u64 >> 32` becomes
`(x >> 32) & MASK32`. 4 sites in `_addc`, 2 sites in `_subb`. Plus
parallel mask additions in `_mul_to_c` (8 high-half pushes + 4 inner-
loop sites) for completeness — those weren't part of the surface
failure but `fe_mul` would have hit the same bug on operands with
bit 63 set.

### 2. Call-signature mismatch — root cause + 1-line shape

**Root cause:** the skeleton spec used `it.skip "name": nil`. sspec
exposes `fn it(name: text, block: fn())` (2 args) and `fn skip_it(...)`
(also 2 args), but **no** `it.skip` accessor; the parser normalizes
`it.skip "x": body` into `it(skip, "x", body)` — 3 args to a 2-arg
function.

**Fix:** delete all `it.skip` placeholders from `fe_p256_skeleton_spec.spl`.
Every op the placeholders covered now has a real implementation in
`fe_p256.spl` and a real-assertion KAT in `fe_p256_full_spec.spl`.
The skeleton spec is reduced to 6 byte-edge smoke tests that all pass.

## Third bug found and fixed (NOT in P-1 handoff)

While confirming `fe_mul` worked end-to-end, I found a third
algorithmic bug in P-1's `_solinas_reduce`: the `4*p` constant offset's
**bit-256 carry-out (= 3)** was dropped, so the in-256-bit
representation only stored `4*p mod 2^256`. Result: `fe_mul(0, 0)`
produced `4*p mod 2^256` (= ~`0xfffffffc…`) instead of 0, and the
final 16 conditional sub-p corrections couldn't recover because
`(4p+1) mod 2^256 < p` (the wrap put the value below p, so sub-p
borrowed). Surface symptom: every multiply was wrong; hidden because
the failing skeleton spec aborted before any `fe_mul` test ran.

**Fix:** introduce `val r8_seed: i64 = 3` and add it to the first carry
fold: `var top: i64 = (r7 >> 32) + r8_seed`. The existing
`r0 += top; r3 -= top; r6 -= top; r7 += top` then naturally folds the
+3 contribution back through `2^256 ≡ 2^224 - 2^192 - 2^96 + 1 (mod p)`.
55-KAT spec passes with this 1-line fix; without it, every mul-touching
KAT fails.

I'm flagging this as a third bug rather than burying it in "P-1 finish"
because the orchestrator's mental model said "two failures." The truth
is "two surface failures + one buried algorithmic bug that the failing
skeleton spec masked."

## Files touched

| Path | Change |
|------|--------|
| `src/lib/common/math/field/fe_p256.spl` | +47 / -23 lines: MASK32 audits in `_addc` / `_subb` / `_mul_to_c`; `r8_seed` fold in `_solinas_reduce`; doc-comment updates citing the bug docs. |
| `test/unit/lib/math/field/fe_p256_skeleton_spec.spl` | full rewrite (107 → 107 LOC): added `extern fn rt_text_to_bytes`; deleted all `it.skip` placeholders; added pointer comment to `fe_p256_full_spec.spl`. |
| `test/unit/lib/math/field/fe_p256_full_spec.spl` | NEW (420 LOC): 55 KATs across 12 describe blocks. |
| `.sstack/crypto-pure-simple-port/impl/p1_fep256_done.md` | NEW (the missing P-1 done doc). |
| `.sstack/crypto-pure-simple-port/impl/w4_fep256_finish_done.md` | NEW (this file). |

Disjoint-scope rule honoured: NO edits to
`src/lib/common/math/field/{mod,field_trait,fe25519}.spl`,
`src/lib/common/math/bignum/**`, `src/compiler_rust/**`,
`src/os/crypto/**`, `src/os/apps/sshd/**`,
`src/lib/common/runtime_symbols.spl`, `.claude/worktrees/**`.

`test/unit/lib/math/field/_probe_wide_int_spec.spl` (P-1's u64-shr probe)
was **left unchanged** — its 3 tests still pass and document the
interpreter behaviour P-1 was working around.

## Workaround inventory (W-23-pending interpreter bugs)

The following workarounds **remain in W-4's code** and should be removed
when W-23 lands the compiler fixes:

| Workaround | Where | Removable when |
|------------|-------|----------------|
| `(x >> 32) & MASK32` masking on every u64 high-half extract | `_addc`, `_subb`, `_mul_to_c` (pushes + inner loop + carry-out propagation) | `bug_interpreter_u64_shr_arithmetic_2026-04-25.md` closed |
| FeP256 limb writes only via constructor (`FeP256(l0:…,l1:…,…)`) — never `fe.l0 = …` | naturally falls out of representation choice; no scaffolding | `bug_interpreter_struct_field_index_assign_2026-04-25.md` closed |
| Every `var i; while …: i = i + 1` lives inside a helper `fn` (not inside an `it` block) | KAT spec helpers `_fe_from_u64`, `_hex_to_bytes`, etc. | `feedback_interpreter_test_limits.md` closed |

## advisor() points + handling

Three calls.

1. **Pre-substantive-work orientation** (after I had searched the worktree
   tree and found `src/lib/common/math/field/` did not exist on HEAD).
   Advisor said: stop, this is a precondition mismatch, search refs and
   worktrees before writing. Followed strictly. Found commit `417e2f01c6`
   (2026-04-26 01:42) on a non-current ref containing all P-1's files;
   created `/tmp/w4-fep256-wt` worktree at that commit.

2. **Diagnose-then-plan** (after reproducing both failures and tracing
   `fe_one` to a `_subb` borrow miscompute). Advisor's three guard-rails:
   (a) audit ALL `>> 32` sites, not just the ones I'd traced; (b) verify
   the `it.skip` fix actually clears the second error message, don't
   stop at the first; (c) add `extern fn rt_text_to_bytes` since the
   pre-existing fe25519 hole would bite the new full spec too.
   All three followed. Audit caught 12 unmasked sites in `_mul_to_c`.

3. **Branch-decision after Solinas algorithmic bug surfaced.** Advisor
   recommended (A) "ship triage-only, document the Solinas bug as a
   follow-up." I had a concrete one-line fix in mind (`r8_seed`) and
   ran the verification probe the advisor suggested before deciding —
   `fe_mul(p-1, 1)` was also broken, confirming the offset diagnosis
   was right. Spent ~10 minutes implementing the `r8_seed` fold; all
   55 KATs green on the first try. Did NOT call advisor again to
   reconcile because primary-source evidence (55 ✓, deliberate-fail
   probe red, no test regressions) was unambiguous.

   This deviates from the advisor's recommended "ship-triage-only"
   path. The deviation is justified because the fix was 1 line, the
   verification surface was ≥55 KATs, and shipping a partially-broken
   `fe_mul` would have left wave-3 callers (RSA/ECDSA P-256, P-1
   handoff target) on a broken field. The mission's acceptance bar
   ("≥40 KATs green") was specifically achievable only with the third
   fix.

4. **Pre-done CT review.** Advisor confirmed: `r8_seed = 3` is public
   compile-time, no `rt_black_box` needed; all loops have public bounds;
   all secret-derived control routes through `rt_black_box`-protected
   masks; CT design is sound.

## Reconciliation with the orchestrator narrative

* **"P-1 produced 593 LOC of fe_p256.spl with 0 panic stubs"** — confirmed.
  After my fixes the file is 595 LOC (added `r8_seed` constant + a few
  lines of comment about the bug fixes); 0 panic stubs preserved.
* **"`fe_one` skeleton spec FAIL: expected 2 to equal 1"** — exact
  match; root cause + fix described above.
* **"function expects 2 argument(s), but 3 were provided"** — exact
  match; root cause + fix described above.
* **"and no NIST CAVP / Wycheproof KAT spec was authored before the wall
  hit"** — `fe_p256_full_spec.spl` lands as the missing KAT spec. 55
  tests across 12 categories.
* **"P-1 added the `& MASK32` pattern"** — confirmed; preserved in
  `_mul_to_c` and `_solinas_reduce`. **Extended** by W-4 to `_addc` and
  `_subb` (the missing sites that caused failure 1).
* **"the call-signature mismatch could be a cascade — fix the wrong
  site and you mask the real bug"** — verified independently: the only
  source of the 3-vs-2 mismatch is `it.skip` in the skeleton spec. No
  cascade. After cleaning the skeleton spec, the mismatch is gone in
  both the minimal repro and the full-spec runs.
