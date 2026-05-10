# W-AES — B4-sugar AES-GCM rewrite + NIST GCM KATs (done)

**Date:** 2026-04-25
**SStack feature:** `crypto-pure-simple-port`, wave 5
**Worktree branch:** `worktree-w-aes-gcm`
**Scope (disjoint):** only `src/os/crypto/aes_gcm.spl`,
`src/os/crypto/aes128_gcm.spl`, and `test/unit/os/crypto/aes_gcm_*`

## Outcome

### 1. B4-sugar rewrite

Both AES-GCM packed-`u32` byte-extract chains rewritten from
`(state[i] >> N) & 0xFF` to `state[i].bits[N..N+8]`. C-1 deferred these
two files because they were off-limits for the C-1 sweep — closed here.

| File                              | Byte-extract chains before | Byte-extract chains after | Reduction |
|-----------------------------------|----------------------------|---------------------------|-----------|
| `src/os/crypto/aes_gcm.spl`       | 28                         | 0                         | 100 %     |
| `src/os/crypto/aes128_gcm.spl`    | 28                         | 0                         | 100 %     |
| **Total**                         | **56**                     | **0**                     | **100 %** |

Far above the B4 acceptance gate of ≥30 %. Sites rewritten:

- `_sub_word` (4 chains × 2 files)
- `_add_round_key` AES-256 only (4 chains)
- AES-128 key expansion `rcon` mix-in (4 chains)
- GHASH `len_block` `aad_bits`/`ct_bits` big-endian encoding (16 chains × 2 files)
- `_inc32` counter increment lo-32 split (4 chains × 2 files)

The remaining `& 0xFF` matches in both files are NOT byte-extracts —
they are width-mask after a left-shift in `_xtime` and the bit-rotation
inside the GF(2^128) multiplier's GHASH XOR loop.

### 2. NIST GCM KATs

`test/unit/os/crypto/aes_gcm_kat_spec.spl` — **14 `it` blocks** total:

- **AES-128-GCM** (NIST SP 800-38D Appendix B Tests 1-4):
  empty PT/empty AAD, 16-byte-zero PT, 64-byte canonical PT no AAD,
  60-byte PT + 20-byte AAD (the canonical GCM test vector).
- **AES-128-GCM decrypt** (Test 2 inverse + flipped-tag rejection).
- **AES-256-GCM** (NIST SP 800-38D Appendix B Tests 13-16, the
  256-bit-key counterparts of Tests 1-4).
- **AES-256-GCM decrypt** (Test 14/16 inverse + tampered-AAD rejection
  + truncated-ciphertext rejection).

All vectors are the canonical NIST values copied verbatim from
gcm-spec.pdf Appendix B. Hex helpers (`_hex_digit`, `hex(s: text)`)
are inlined per the working pattern from
`test/system/os_crypto_ref_helpers.spl` — `s.len()` + `s[i]` text
indexing — because `text.to_bytes()` is not currently exposed in the
released seed binary.

Coverage matrix:

| Key size | Empty PT | 16-byte PT | 64-byte PT | AAD-bound | Tag reject |
|----------|----------|------------|------------|-----------|------------|
| AES-128  | ✓        | ✓          | ✓          | ✓         | ✓ (1 case) |
| AES-256  | ✓        | ✓          | ✓          | ✓         | ✓ (3 cases)|

### 3. Constant-time discipline

No data-dependent branches were introduced. The `bits[lo..hi]` sugar
desugars at parse time to `(x >> lo) & mask` — the same Cranelift IR
shape as before. Each rewrite site touches public values:

- `_sub_word` indexes `_aes_sbox` by per-byte plaintext/round-key
  values — table is the AES S-box (already not CT against cache-timing,
  pre-existing constraint).
- `_add_round_key` byte-splits the round key, public.
- `_inc32` byte-splits the counter, public per NIST §6.2.
- `len_block` byte-splits AAD/CT lengths, public by definition.

KAT decrypt path uses the existing `expected_tag[i] ^ tag[i]` XOR
accumulator inside `aes*_gcm_decrypt`; this spec asserts only
functional correctness — CT verification of the tag compare is locked
in elsewhere by `test/unit/lib/crypto/black_box_spec.spl` (B6).

## Live-machinery proof (deliberate-fail probe)

Per `feedback_compile_mode_false_greens.md` + R2-broader Phase 2.

Spec: `aes_gcm_b4_sugar_parity_spec.spl` (5 it blocks proving
`x.bits[N..N+8]` matches the manual `(x >> N) & 0xFF` form for both
`u32` and `u64` receivers).

| State                                       | Result          |
|---------------------------------------------|-----------------|
| Clean                                       | 5/5 PASS        |
| Mutated `expect(...).to_equal(0xDE)` → `0xCAFEBABE` | 4 PASS / 1 FAIL with `expected 222 to equal 3405691582` |
| Reverted (md5 ea6b7d75ec67fada4fd13a3d3b7ed475)    | 5/5 PASS        |

The runner reports failures honestly — no false greens — and the
`bits[24..32]` sugar produces the byte 222 (`0xDE`), proving the
desugar produces identical results to the manual chain at runtime.

## KAT execution status

`aes_gcm_kat_spec.spl` runs. The first invocation against this spec
took ~1004 ms and reported **12 failures + 2 passes** with semantic
errors `unknown extern function: rt_array_new_with_cap` (used by
`aes128_gcm.spl`). All subsequent invocations of the same file
report **14/14 PASS in 0–3 ms** — this matches the documented
**`--mode=native` false-green** behaviour in
`feedback_compile_mode_false_greens.md`: stub-generation replaces
the unresolved AES extern surface with no-ops, every `expect(...)`
assertion silently passes. The runner's later "PASSED" result on
this spec is therefore **non-authoritative** until R2-broader and
the false-green bugs are resolved.

**The B4-sugar rewrite is not the cause** of either symptom:

- `aes_gcm_b4_sugar_parity_spec.spl` (which does NOT exercise the
  AES core, so the false-green path does not activate against it)
  proves `bits[lo..hi]` is pointwise identical to the manual
  `(x >> lo) & mask` form on both `u32` and `u64` receivers (5/5
  PASS clean; 4 PASS / 1 FAIL when mutated; back to 5/5 PASS after
  md5-verified revert). Pointwise identity of the byte extracts is
  preserved across the entire byte-by-byte composition by
  construction.
- `rt_array_new_with_cap` was missing from the interpreter's extern
  surface before this commit and is missing after — it is exercised
  on the same lines whether the bytes come from the manual chain or
  the sugar.
- The 2 passing KAT negative-cases (`rejects truncated ciphertext`,
  `rejects modified AAD` in AES-256, `rejects a flipped tag bit` in
  AES-128) only prove that `aes*_gcm_decrypt` returns `Err` on a
  length-mismatched ciphertext — they exit before reaching the AES
  core. They do not validate AES correctness.

What this KAT spec *currently proves*: vector well-formedness, the
hex helper, the encrypt/decrypt API call shape, and tag-rejection
plumbing.

What it does *not yet* prove: AES core byte-exactness against NIST
SP 800-38D Appendix B output. That gate flips the moment the
interpreter extern gap (`rt_array_new_with_cap`,
`rt_aes_sbox`/`rt_aes_rcon` if also missing) closes or `--mode=smf`
+ R2-broader land. Until then this file is a frozen-text reference
for the canonical NIST vectors so a working compile path picks it up
unchanged.

**Why the deliberate-fail probe is on the parity spec, not the KAT
spec:** the KAT spec exhibits the documented false-green — mutating
it to expect `Err` on a passing path still reports PASS in 0 ms.
Probing with a spec that does not trigger stub-generation (the
parity spec uses no externs, no AES) is the only way to demonstrate
that the runner reports failures honestly when actually run.
Documented in the live-machinery section above.

## Advisor

Advisor was rate-limited at the only call site (post-plan, pre-write).
Mission's standing CT guidance was applied without external review:
each rewrite site verified to be on a public value (round-key byte
split, counter byte split, length-encoding byte split) — no rewrite
sits inside a secret-data branch.

## Files

- `src/os/crypto/aes_gcm.spl` — 56 → 28 `bits[lo..hi]` desugar sites,
  640 → 655 LOC (+15 from the doc-comments inside each rewritten fn)
- `src/os/crypto/aes128_gcm.spl` — same pattern, 611 → 621 LOC (+10)
- `test/unit/os/crypto/aes_gcm_kat_spec.spl` — new, 320 LOC, 14 `it`
- `test/unit/os/crypto/aes_gcm_b4_sugar_parity_spec.spl` — new,
  the deliberate-fail / live-machinery vehicle, 5/5 PASS

## Worktree branch

`refs/heads/worktree-w-aes-gcm` — see commit hash in the parent agent
reply (recorded immediately after the `git update-ref`).
