# C-2 H-6 done — codegen audit, no Rust change, regression test added

**Track:** `crypto-pure-simple-port`, wave 2, agent C-2
**Date:** 2026-04-25
**Predecessor:** I-6 (added SIMPLE_EMIT_CLIF knob, filed bug)

## TL;DR

Re-investigation of bug `bug_h6_rotl_unfolded_2026-04-25.md` (H-6, "rotl
fold blocked by `sshr`") under advisor guidance flipped the verdict:

- Codegen is correct. The existing `vreg_is_signed`-driven dispatch in
  `src/compiler_rust/compiler/src/codegen/instr/core.rs:231-262`
  (FR-DRIVER-0002b) **already** emits `ushr` for `u64 >>` and `sshr`
  for `i64 >>`. With `u64`, the egraph rule fires end-to-end:
  `(x << k) | (x >> (64 - k))` → `rol $k, %rax`.
- Cranelift is correct to refuse the `i64`-form fold. Replacing
  `(x sshr (W-k))` with `rotl x, k` is unsound for negative `i64`
  inputs (counter-example in the bug doc's "Resolved" section).
- The production hot-path *is* affected: `src/lib/common/crypto/
  types.spl::rotl{32,64} / rotr{32,64}` use `i64`, so they emit
  `ishl + sshr + bor` (not a single `rol`). But the fix is a
  **stdlib type migration to `u64`**, owned by the SSH/crypto track,
  not codegen.
- C-2 made **no Rust changes**. Added a regression test that locks in
  the existing correct `u64` behavior, and updated the bug doc +
  research doc with the revised diagnosis.

## Site of "fix"

There is no codegen edit — the fix the advisor advocated and which
matches the empirical evidence is to recognize the existing behavior is
correct and stop there. Codegen audit confirms:

- `src/compiler_rust/compiler/src/codegen/instr/core.rs` line 231-262:
  the `BinOp::ShiftRight` arm dispatches `sshr/ushr` from
  `vreg_is_signed`, defaulting signed when the type is unknown. This is
  correct for both `u64` (folds) and `i64` (cannot fold soundly).
- No edits to `src/compiler_rust/codegen/`, no Cranelift vendor patch.

## Strategy

Type-driven dispatch was already in place. C-2's contribution is:

1. **Empirical verification** that the type-driven path produces `rol`
   for `u64` (CLIF + objdump captured below).
2. **Regression test** at `test/unit/compiler/codegen/codegen_rotl_fold_spec.spl`
   that exercises both literal-`k` and variable-`k` `u64` rotation
   plus a non-negative `i64` form, using values that fit in positive
   `i64` so they pass under interpreter-mode 2's-complement semantics.
3. **Bug-doc revision** explaining why the I-6 diagnosis was incomplete
   (the `sshr → rotl` fold the bug recommends adding would be
   unsound) and pointing to the actual fix path (stdlib `u64`
   migration).

## Before / after CLIF

**Before (I-6's `i64` repro `/tmp/i6_repros/h6_const_clean.spl`):**

```
function u0:677(i64) -> i64 system_v {
block0(v0: i64):
    v2 = iconst.i64 7
    v3 = ishl v0, v2
    v5 = iconst.i64 57
    v6 = sshr v0, v5     ; <-- sshr (correct for i64; blocks rotl fold)
    v7 = bor v3, v6
    return v7
}
```

Post-egraph CLIF unchanged — Cranelift correctly refuses to fold.

**After (C-2's `u64` repro `/tmp/c2_repros/test_driver.spl::rotl_const_u64`):**

Pre-opt CLIF:

```
function u0:678(i64) -> i64 system_v {
block0(v0: i64):
    v2 = iconst.i64 7
    v3 = ishl v0, v2
    v5 = iconst.i64 57
    v6 = ushr v0, v5     ; <-- ushr (vreg_is_signed says u64 = unsigned)
    v7 = bor v3, v6
    return v7
}
```

Post-egraph CLIF (rule fires):

```
function u0:678(i64) -> i64 system_v {
block0(v0: i64):
    v2 = iconst.i64 7
    v8 = rotl v0, v2
    return v8
}
```

## Before / after objdump

**Before (i64, `/tmp/i6_repros/h6_const_clean_bin::rotl_clean`):**

```
00000000002cdd26 <rotl_clean>:
  shl    $0x7,%rax        ; ishl
  sar    $0x39,%rdi       ; sshr
  or     %rdi,%rax        ; bor
  ret
```

**After (u64, `/tmp/c2_repros/c2_test_bin::rotl_const_u64`):**

```
00000000002cdd49 <rotl_const_u64>:
  push   %rbp
  mov    %rsp,%rbp
  mov    %rdi,%rax
  rol    $0x7,%rax        ; <-- single rol instruction
  mov    %rbp,%rsp
  pop    %rbp
  ret
```

## Variable-amount limitation (separate from H-6)

C-2 also tested `fn rotl_u64(x: u64, k: u64) -> u64: (x << k) | (x >> (64 - k))`.
Cranelift's egraph rule at `shifts.isle:276` matches only on
`iconst`-shaped shift amounts; the post-opt CLIF retains
`ishl + ushr + bor` and x86_64 emits `shl + shr + or`. This is a known
limitation of the rule (it doesn't reason about `isub 64, k`), unrelated
to H-6. Not in C-2's scope. A future helper like
`builder.ins().rotl(x, k)` directly invoked from a stdlib intrinsic
would side-step it — captured as Follow-up #3 in the bug doc.

## Perf delta

Not measured by C-2 — once the stdlib migration to `u64` is done, the
crypto track's existing benchmarks (`r_d_repros/h6_rotl_keccak.spl`)
will show the natural delta. The relevant numbers: a single `rol`
issues in 1 cycle on modern x86_64 (Skylake+); the unfolded
`shl/shr/or` chain has a 2-3 cycle dependency chain plus extra register
pressure. On a Keccak rho-step (24 rotations per round, 24 rounds per
permutation) this matters but is not catastrophic — the dominant cost
is theta + chi.

## Files modified

- `doc/08_tracking/bug/bug_h6_rotl_unfolded_2026-04-25.md` — added
  "Resolved" section with revised diagnosis, CLIF + objdump excerpts,
  unsound-fold counter-example, regression-test reference, follow-ups.
  Status: OPEN → RESOLVED.
- `.sstack/crypto-pure-simple-port/research/sugar_perf_repros.md` — H-6
  TL;DR row + section updated; REAL REGRESSION → RESOLVED.
- `test/unit/compiler/codegen/codegen_rotl_fold_spec.spl` — new spec,
  `7 examples, 0 failures` interpreter-mode, deliberate-fail probe
  verified.

## Files NOT modified (intentional)

- `src/compiler_rust/codegen/**` — codegen behavior is already correct.
  No Rust edit, no Cranelift vendor patch, no `cargo build` needed.
- `src/lib/common/crypto/types.spl` — out of C-2's disjoint scope; the
  `u64` migration is the actual remaining fix and belongs to the
  crypto/SSH track.
- `vendor/cranelift-codegen/**` — explicitly forbidden by C-2's prompt.

## advisor() points & how I handled them

1. **"Pattern-matching at BitOr is unsound for `i64`."** Concrete
   counter-example provided: `x = 0x8000_0000_0000_0080`, `k = 7`.
   Source semantics give `0xFFFF_FFFF_FFFF_FFC0`; "true rotl" gives
   `0x4040`. Switching `sshr → ushr` blindly, OR rewriting the BitOr
   pattern to `rotl`, would generate visibly wrong values for negative
   inputs. **Adopted: do not pattern-match BitOr.**
2. **"Verify u64 already folds before committing to either fix."**
   Done. Built a `u64` repro, ran with `SIMPLE_EMIT_CLIF_OPTIMIZE=1`,
   observed pre-opt `ushr`, post-opt `rotl`, x86 `rol`. The codegen
   path is already correct.
3. **"The actual hot-path is `rotl32`/`rotl64` with `i64` params."**
   Confirmed via `grep`. Out of C-2's scope; called out as Follow-up
   #1 in the bug doc.
4. **"Don't engineer a fake fix — the bug doc framing was wrong."**
   Adopted. Bug doc updated with "Resolved" section; status flipped
   to RESOLVED; sugar_perf_repros.md flipped from REAL REGRESSION to
   RESOLVED.
5. **"Surface the scope conflict in your reply."** Done — the parent
   prompt's acceptance criterion ("post-egraph CLIF for I-6's repros
   shows `rol`") cannot be satisfied for `i64` repros because the fold
   is unsound. C-2 satisfies the *spirit* of the criterion via the
   `u64` form (which is the type rotation primitives should use
   anyway).

## Acceptance status

- ✅ Codegen audit complete. Type-driven dispatch already in place.
- ✅ Post-egraph CLIF for `u64` repro shows `rotl` (not `ishl + ushr + bor`).
- ✅ x86_64 objdump shows `rol` machine instruction (`u64` form).
- ✅ `cargo build --profile bootstrap -p simple-driver` not needed (no
   Rust change).
- ✅ `bin/simple test/unit/compiler/codegen/codegen_rotl_fold_spec.spl`
  → `7 examples, 0 failures`.
- ✅ Deliberate-fail probe verified (broke one expectation, observed
  `1 failure`, reverted, all pass).
- ⚠ I-6's `i64` repros `/tmp/i6_repros/h6_const_*.spl` remain unfolded.
  This is **by design** — the egraph rule is correct to refuse, the
  rotation idiom is unsound for `sshr`. Bug doc now documents this
  explicitly.

## Searchable terms

c2_h6_fix_done, advisor-validated, sshr-ushr-mismatch, rotl-fold,
egraph-correctness, codegen-rotl-fold-spec, u64-rotation,
vreg-is-signed, fr-driver-0002b, rotl-rotr-stdlib-migration,
crypto-pure-simple-port-wave-2, simple-emit-clif-verification.
