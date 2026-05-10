# B7 Sugar/Perf Hunt-list — R-D Research Report

Date: 2026-04-25
Owner: R-D (parallel SStack research fan-out)
Companion to: `doc/08_tracking/todo/compiler_bugs_for_crypto_2026-04-25.md` §B7
Repros: `/tmp/r_d_repros/`

Interpreter floor (empty `fn main(): print("hi")`): ~0.025 s. Subtract from
small-N timings.

## TL;DR

| id  | verdict                                | repro                               | measurement (interp wall)                              | follow-up                  |
|-----|----------------------------------------|-------------------------------------|--------------------------------------------------------|----------------------------|
| H-1 | API absent — feature request           | n/a (`u32.to_be_bytes` not in stdlib)| —                                                      | stdlib feature, not B7     |
| H-2 | verified fine (const IS hoisted)       | h2c_aes_sbox_const.spl              | const=0.28s ≈ shared=0.27s  (rebuild=0.33s, +27%)      | none — close               |
| H-3 | API absent — feature request           | n/a (no `u64.mul_hi`)                | —                                                      | stdlib feature, not B7     |
| H-4 | API absent — feature request           | n/a (no `clmul` / `gf128_mul`)       | —                                                      | stdlib + intrinsic, not B7 |
| H-5 | duplicate of B2 — quadratic confirmed  | h5{b,c,_,d}_u64_push.spl             | N: 1k=0.04s · 2k=0.06s · 4k=0.15s · 8k=0.50s (≈O(N²))  | covered by B2; cite only   |
| H-6 | RESOLVED — diagnosis revised (C-2). Codegen is correct; `u64` already folds end-to-end (`rol`); `i64` *cannot* fold soundly. Stdlib must migrate `rotl{32,64}` to `u64`. | h6_const_clean (i64, no fold), h6_u64_clean (u64, folds) | u64: pre `ushr`, post `rotl`, x86 `rol`; i64: pre `sshr`, no fold (correct) | bug_h6_rotl_unfolded_2026-04-25.md updated; codegen_rotl_fold_spec.spl added |
| H-7 | verified fine (`for byte` ≈ index)     | h7{,b,c,d}_for_byte/index.spl        | 5k: for=0.21 idx=0.22 · 50k: for=20.8 idx=19.9         | KAT-loader slowness is B2  |
| H-8 | verified fine (clean diagnostic)       | h8_extern_unknown.spl                | `error: semantic: unknown extern function: …` rc=8     | none — close               |

**0 new bug docs filed.** All speculative items are duplicates, missing
APIs, deferred, or verified fine.

---

## H-1 · `u32.to_be_bytes` not folded — API absent

`grep -rn 'to_be_bytes' src/lib --include='*.spl'` → 0 matches. Method
doesn't exist on integer types today; SHA-256 message scheduling uses
hand-rolled `get_byte` / shift-and-mask via `std.bitwise_utils`. Therefore
not a perf regression, but a **stdlib feature request** for the crypto
port. Not a B7 bug. Suggest the §1 SHA-256 task open a feature request
for `to_be_bytes` / `from_be_bytes` if the round-code clarity matters.

## H-2 · const `[u8;256]` AES S-box — verified FINE

Three variants, N = 5000 sub_bytes calls over a 16-byte block:

| variant                        | wall  | repro                          |
|--------------------------------|-------|--------------------------------|
| sbox built **inside fn**       | 0.33s | h2_aes_sbox.spl                |
| sbox passed as **fn arg**      | 0.27s | h2b_aes_sbox_shared.spl        |
| **module-level `val SBOX`**    | 0.28s | h2c_aes_sbox_const.spl         |

Module-level `val SBOX = [...]` matches the `shared-arg` baseline (0.28 ≈
0.27) — the table is **not** re-initialized per call. The 27 % overhead
in the inner-build variant is real but expected (256-element list
allocation per call ≈ 14 µs in the interpreter). **Verdict:** no
regression. Close. Style guidance: AES code should declare the S-box
once at module scope, not inside `sub_bytes`.

## H-3 · `u64.mul_hi` libcall — API absent

No `mul_hi` / `umulh` method on `i64` / `u64` in the stdlib (grep clean).
Curve25519 will need either a 128-bit intermediate or carry-chains in
26-bit limb form. Not a perf-regression bug; **stdlib feature request**.

## H-4 · GF(2^128) carryless mul — API absent

No `clmul`, `gf128_mul`, `carryless` symbols in the codebase. GCM ghash
will be quadratic-shift-and-xor without an intrinsic. **Feature request
+ codegen intrinsic**, not a B7 regression.

## H-5 · `[u64].push` quadratic — duplicate of B2

| N    | wall  | (N−floor)/(prev N−floor) | repro                       |
|------|-------|--------------------------|-----------------------------|
| 1024 | 0.04s | —                        | h5b_u64_push_small.spl      |
| 2048 | 0.06s | 2.3×                     | h5c_u64_push_med.spl        |
| 4096 | 0.15s | 3.6×                     | h5_u64_push.spl             |
| 8192 | 0.50s | 3.8×                     | h5d_u64_push_8k.spl         |

Each doubling of N raises wall-clock ~3.7× — clear quadratic shape.
**Already tracked as B2** ("Interpreter `[u8]` quadratic on multi-MiB
buffers"); same growth confirmed for `[i64]`. The B2 fix (already-landed
`rt_bytes_alloc` for `[u8]`) needs an analogue for typed numeric vectors,
or B2's deeper "fix amortized doubling in the interpreter `push` lowering"
path. **No new bug doc.**

## H-6 · Keccak `rotl(x, n)` folding — RESOLVED 2026-04-25 by C-2

**Diagnosis revised.** I-6 (2026-04-25) added the `SIMPLE_EMIT_CLIF` knob
and confirmed `i64` repros never fold. C-2 (wave 2, 2026-04-25)
re-investigated under advisor guidance and reached a different
conclusion: **codegen is correct, the bug is in stdlib type choice.**

- `u64` rotation (the *actually correct* type for rotation) already
  folds end-to-end. Pre-opt CLIF emits `ushr`, post-egraph collapses to
  `rotl`, x86_64 emits a single `rol` instruction. Verified with
  `SIMPLE_EMIT_CLIF=... SIMPLE_EMIT_CLIF_OPTIMIZE=1`. (See bug doc
  "Resolved" section for the CLIF + objdump excerpts.)
- `i64` rotation (what I-6's repros + `src/lib/common/crypto/types.spl`
  use) does **not** fold, and Cranelift is correct to refuse —
  `(x sshr (W-k))` is not a rotation for negative `i64`. Counter-example
  in the bug doc.
- Therefore the production fix is to migrate
  `src/lib/common/crypto/types.spl::rotl{32,64} / rotr{32,64}` and
  callers (`legacy_hash`, `sha256`, `sha512`, …) from `i64` to `u64`.
  That work is owned by the crypto/SSH track, **not** codegen.

C-2 added `test/unit/compiler/codegen/codegen_rotl_fold_spec.spl` to lock
in the existing correct `u64` behavior; runs `7 examples, 0 failures`,
deliberate-fail probe verified.

I-6's earlier work on the same item:

Verdict: **real codegen regression**, but the root cause is *not* what the
B7 hunt-list said. Simple has no native `rotl` operator to "fold"; the
canonical idiom `(x << k) | (x >> (W - k))` is supposed to be recognized
by Cranelift's egraph rule at
`vendor/cranelift-codegen/src/opts/shifts.isle:271`. That rule requires the
right-shift half to be **`ushr`** (logical), but Simple's `ShiftRight` for
the default signed `i64` lowers to **`sshr`** (arithmetic). So no fold
ever happens. CLIF post-egraph still shows `ishl + sshr + bor`, never a
single `rotl`.

Filed: `doc/08_tracking/bug/bug_h6_rotl_unfolded_2026-04-25.md` with full
CLIF excerpts, primary-source ISLE rule, three repros, and a fix sketch
(cheapest path: add a `rotl`/`rotr` stdlib intrinsic that lowers directly
to `builder.ins().rotl(...)`).

Original interpreter measurement (5000 × 25 rotl @ N=7 = 1.05 s) is kept
as historical interpreter baseline; the actual bug lives in compiled mode.

## H-7 · `for byte in bytes:` overhead — verified FINE

Same buffer, two iteration styles:

| N      | for-byte | index-while |
|--------|----------|-------------|
| 5,000  | 0.21 s   | 0.22 s      |
| 50,000 | 20.83 s  | 19.90 s     |

`for byte` is statistically indistinguishable from index-while in the
interpreter. The N = 50 k blow-up is dominated by the `push` build of
`buf` (H-5 / B2), not the iteration. **Verified fine; close.** KAT
loaders should still avoid push-loops, but for the B2 reason, not H-7.

## H-8 · Unknown extern silent NoOp — verified FINE

Repro `h8_extern_unknown.spl`:

```
extern fn rt_does_not_exist_h8(x: i64) -> i64
fn main():
    val r = rt_does_not_exist_h8(42)
    print("called_rc=" + r)
```

`bin/simple` output:

```
error: semantic: unknown extern function: rt_does_not_exist_h8
rc=8
```

Diagnostic surfaces clearly with non-zero exit code. The
`feedback_extern_bootstrap_rebuild.md` failure mode (silent NoOp)
referred to a *cached/stale* release binary that hadn't been
re-bootstrapped, not to the diagnostic-emission pipeline itself. The
machinery is intact. **Close.** Process guidance — always
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` after extern
additions — remains the relevant mitigation.

---

## Cross-cutting recommendations

The single highest-leverage fix is still **B2's amortized-growth path
in the interpreter `push` lowering** — both `[u8]` and `[i64]` exhibit
identical quadratic shape, so the proper fix (not the `rt_bytes_alloc`
quick patch) generalizes across all KAT loaders, RSA limb buffers, and
buffered crypto state. After that, the **codegen folder/MIR optimizer**
is the unverified surface: H-1, H-3, H-4, H-6 all live there, and three
of them currently can't even be measured because the *front-end stdlib*
lacks the API. The pragmatic order is: (a) finish B2 properly, (b) add
`to_be_bytes` / `from_be_bytes` / `mul_hi` to `std.bitwise_utils` so
crypto code stops hand-rolling, then (c) re-open H-6 with compiled-mode
IR inspection. The interpreter itself is **not** a B7 contributor outside
B2 — `for byte` and unknown-extern paths both work as expected.

---

## Top-3 leverage fixes (estimated speedup × ease)

1. **B2 amortized-doubling in interpreter `push`** (already tracked).
   Quadratic → linear; unblocks every multi-MiB KAT loader and any
   limb-vector grown incrementally. Ease: medium (fix in interpreter,
   not codegen). Speedup: 30–100× on multi-MiB buffers.
2. **Add `to_be_bytes` / `from_be_bytes` / `mul_hi` stdlib helpers**
   (covers H-1, H-3 surface). Ease: low (pure-Simple stdlib + `i64`
   bitops). Speedup: code-clarity-driven; sets up future intrinsic
   lowering. Replaces hand-rolled mask/shift in SHA-256, Curve25519.
3. **Compiled-mode IR inspection knob + H-6 re-test**. Ease: low if a
   `--emit=ir` already exists; medium if not. Without it, every H-N item
   that lives in codegen is unverifiable.

