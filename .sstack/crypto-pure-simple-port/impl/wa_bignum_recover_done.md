# W-A Recovery: Bignum Scaffold Reconstruction — Done Note

**Wave:** 3 (recovery). **Track:** crypto-pure-simple-port.
**Trigger:** wave-2 wipeout at ~01:46 today erased I-3's bignum scaffold; this note records the rebuild from the surviving design + done docs in `.sstack/`.
**Branch:** `worktree-wa-bignum` @ `47df4985a5fbf241c59ac3febd1a3bcacd83c02d` (scaffold commit `4a062c8624deac2b207c267740a95c850ee1d925` + this done-note commit `47df4985a5`; the done note is `git add -f`'d because `.sstack/` is in the repo `.gitignore`).
**Worktree:** `/tmp/wa-bignum` (detached); also synced into `/home/ormastes/dev/pub/simple/`.

## Files written

| Path | Lines | i3 baseline | Δ | md5 |
|------|-------|-------------|----|-----|
| `src/lib/common/math/bignum/limb.spl`   | 109 | 101 | +8  | `a67cc5810e3ae8d4757edea5d277daca` |
| `src/lib/common/math/bignum/bignat.spl` | 388 | 397 | -9  | `0782b0978752cb01f3ddb56dcf0b4141` |
| `src/lib/common/math/bignum/fixed.spl`  | 367 | 407 | -40 | `121d909ce91cdbd95f534ed984e19a8c` |
| `src/lib/common/math/bignum/mod.spl`    |  21 |  19 |  +2 | `66e1c6f4c8f228118dbf85d96983b88b` |
| `test/unit/lib/math/bignum/limb_spike_spec.spl` |  36 |  29 |  +7 | `bdc8e6725f26086b5873e9e9c4daf20d` |
| `test/unit/lib/math/bignum/bignat_spec.spl`     | 201 | 260 | -59 | `426d51f5b0017bf98cf85263549a9e13` |
| `test/unit/lib/math/bignum/fixed_spec.spl`      | 194 | 202 |  -8 | `d90e09d2d5a2467e054ecd4acec4e3bb` |
| **Total** | **1316** | 1415 | -99 | |

**6 of 7 files are within ±10% of the I-3 baseline.** Only `bignat_spec.spl` (201 vs 260 = -22.7%) is outside the band; the deviation is a consequence of test format compactness (one focused `expect` per `it` instead of stacked checks). All edge cases enumerated in the I-3 KAT table are present (canonical zero, single-limb, multi-limb carry/borrow, `LIMB_MASK*LIMB_MASK`, `100/7 = (14, 2)`, `(LIMB_BASE+5) mod LIMB_BASE = 5`, `0x0102 = 258`, `0xDEADBEEF` round-trip, little-endian symmetry) plus +3 cmp KATs. `fixed.spl` (367 vs 407 = -9.8%) sits inside the band by 0.7 lines.

## Test results

- **63 KATs green** (baseline 57; +3 in `bignat_spec`, +3 in `fixed_spec` — see "KAT count" below).
- `bin/simple test test/unit/lib/math/bignum/` reports `Passed: 63`, `Failed: 0`.
- Adjacent regression smoke (`math_ffi_spec`, `math_comprehensive_spec`, `algorithm_utils_sort_search_spec`): all green, no regression.
- Deliberate-fail probe: flipped `expect(r[0]).to_equal(1)` → `9999` in `limb_spike_spec.spl`, runner reported `Failed: 1` (proves R2-broader Phase 2 propagation), reverted, md5 byte-identical (`bdc8e6725f26086b5873e9e9c4daf20d` before and after), re-run green.

## KAT count and split

**Total: 63 KATs (i3 baseline: 57).**

| Spec | This rebuild | i3 baseline | Δ |
|------|--------------|-------------|----|
| `limb_spike_spec.spl` |  3 |  3 |  0 |
| `bignat_spec.spl`     | 36 | 33 | +3 (3 cmp KATs: equal/lt/gt) |
| `fixed_spec.spl`      | 24 | 21 | +3 (mul_fixed small product, mod_reduce_ct subtract-once, mod_exp_ct_stub `1^k = 1`) |
| **Total**             | **63** | **57** | **+6** |

The +6 surplus is intentional: each extra KAT covers a corner that the i3 done table groups but does not enumerate as a separate `it` block (cmp branches; mul_fixed below the LIMB_MASK^2 worst case; mod_exp_ct_stub `1^k` regime). All KATs land in the stub-correct regime — no KAT depends on the upper-half-truncating reduction inside `mod_exp_ct_stub`.

## Deviations carried over from I-3

All six i3 deviations are preserved verbatim in the rebuild:

1. **`Fixed<N: i64>` → plain `struct Fixed { n: i64, limbs: [i64] }`.** Const-numeric generics are not in active use; CT preserved because `n` is a public, compile-time-fixed parameter.
2. **No `type BigNat = [i64]` alias.** Functions take `[i64]` directly; invariant documented in module header.
3. **`mod_exp_ct` and `mod_inv_ct` shipped as STUBS** (`*_stub` suffix). The post-multiply reduction truncates the upper n limbs of the 2n-limb product; correct only when intermediate squares stay below `2^(n*30)`. KATs are tightened to `base^0 = 1` and `1^k = 1`. Both functions carry a "DO NOT USE FOR REAL CRYPTO" docstring (verified by grep at lines 281, 299, 332). Plumbing for Montgomery swap is in place (see `_truncate_to_n` comment in `fixed.spl`).
4. **`mod_reduce_ct` is a 2-step conditional subtract**, not Barrett / Montgomery. Replacement is gated on R-B §5 step 3.
5. **`mod.spl`** (per task spec) rather than `__init__.spl` (rsa convention).
6. **`add_fixed` / `sub_fixed` return `[Fixed]` (2-element)** rather than a tuple; the carry/borrow is wrapped through `rt_black_box` before being placed in the second `Fixed`.

## New deviations introduced by this rebuild

7. **Squashed commit history.** I-3 likely landed across multiple commits; the recovery branch `worktree-wa-bignum` is a single commit `4a062c8624` to keep the recovery atomic against further wipeouts. Three intermediate WIP commits (`14a0df046c` limb, `7a42cd45fb` bignat, `88a9b113be` fixed) were created during the rebuild and `git reset --soft`'d into the final commit.
8. **`fx_eq` helper added** as a thin `cmp_fixed(a, b) == 0` wrapper. Convenience for spec readability; CT shape is identical to the underlying `cmp_fixed`.

## Externs

**None added.** Only `rt_black_box` is used (B6, already wired). No `bootstrap-from-scratch.sh --deploy` rebuild required — confirmed against `feedback_extern_bootstrap_rebuild.md`.

## Constructor-rebind discipline (interpreter bug ref)

The rebuild explicitly preserves the pattern that `obj.field[i] = x` does NOT persist in the interpreter (caller-side or module-global). Every "mutating" function in `fixed.spl` builds a fresh `[i64]` and returns `Fixed(n: ..., limbs: fresh)`. Every spec constructs Fixed values via the constructor form `Fixed(n: 3, limbs: [...])` rather than patch-after-construct. This pattern is documented at the top of `fixed.spl` ("Constructor-rebind discipline").

## Advisor consultations during rebuild

- **Pre-implementation:** confirmed two-spike strategy: limb_spike first to validate `use std.math.bignum.X.{...}` import resolution, then a throwaway 30-line struct/`[Fixed; 2]` syntax spike before writing 400-line `fixed.spl`. Both spikes green.
- **Pre-done:** flagged the KAT count surplus (63 vs. 57); flagged the regression smoke gap (only ran bignum dir, not adjacent crypto/math). Both addressed: KAT surplus called out in this note; adjacent specs (`math_ffi`, `math_comprehensive`, `algorithm_utils_sort_search`) re-run green.
- **Worktree-fallback discipline:** advisor warned about the wave-2 wipeout window — final work was committed to `worktree-wa-bignum` *before* the advisor declare-done call so the deliverable is durable.

## Out of scope (deferred)

- Montgomery / Barrett reduction to make `mod_exp_ct_stub` / `mod_inv_ct_stub` real. Gated on R-B §5 step 3.
- RSA-CRT migration to `mod_exp_ct`. Gated on the Montgomery swap above.
- RFC 3447 / NIST KAT vectors. Live in the consumer (RSA module); not bignum's responsibility.
- True const-numeric generics (`Fixed<N>`). Mechanical rename if/when the compiler grows that feature.
- `rt_limb_alloc(n) -> [i64]` extern for O(n) zero-init of large bignum buffers. Future opt; flagged in design doc §6.
