# C-1 · B4-sugar (`int.bits[lo..hi]`) — done

**Status:** Already implemented on `main` before this agent started. No new work landed.

## TL;DR

When this agent started, `main` already contained commit
`4d627e31da feat(parser): add 'int.bits[lo..hi]' get/set sugar (B4-sugar)`
plus a duplicate-track sibling commit `6521bd2cf8` with identical
title/body. The implementation is in the **Rust seed parser**
(`src/compiler_rust/parser/src/expressions/bitfield.rs` + adjustments
in `postfix.rs` / `no_paren.rs`), the spec is at
`test/unit/compiler/bitfield_sugar_spec.spl` (15 tests), and the doc
entry is in `doc/07_guide/quick_reference/syntax_quick_reference.md`
("Bitfield Slicing" subsection, 35 lines).

This `done.md` records the verification work and the disjoint-scope
reason no parallel-track AES rewrite was attempted.

## Architecture choice (already made by the earlier landing)

The earlier commit chose **parse-time desugar to inline shift+mask**, not
"new EXPR variant" and not "lower to `extract_bits`/`insert_bits`
helper calls." That matches the spec's own docstring:

    Read   :  x.bits[lo..hi]      ->  (x >> lo) & ((1 << (hi - lo)) - 1)
    Write  :  x.bits[lo..hi] = v  ->  x = (x & ~(mask << lo)) | ((v & mask) << lo)

    Strategy: parse-time desugar in the parser so that both the interpreter
    and the HIR-lowering paths see only plain Binary{Shr/Shl/BitAnd/BitOr}
    nodes — no new AST or HIR variant, no 42-file HirExprKind cascade.

The brief asked for a lowering to `extract_bits` / `insert_bits` helper
calls. The earlier commit deviated by lowering to inline binary ops
instead — a strict superset (the helpers are still available in
`std.bitwise_utils` for callers that prefer a function form). I concur
with the deviation: inline lowering avoids a `use std.bitwise_utils`
import in kernel-adjacent code and matches the spec author's intent.

## Files of record (all already in `main`, all M/A in working tree
relative to detached HEAD)

| Path | Status | Lines |
|------|--------|-------|
| `src/compiler_rust/parser/src/expressions/bitfield.rs` | A | 138 |
| `src/compiler_rust/parser/src/expressions/postfix.rs`  | M | +29 |
| `src/compiler_rust/parser/src/expressions/no_paren.rs` | M | +17 |
| `src/compiler_rust/parser/src/expressions/mod.rs`      | M | +1  |
| `src/compiler_rust/compiler/src/codegen/common_backend.rs` | M | +65 |
| `src/compiler_rust/compiler/src/interpreter/expr/calls.rs` | M | +76 |
| `test/unit/compiler/bitfield_sugar_spec.spl`           | A | 112 |
| `doc/07_guide/quick_reference/syntax_quick_reference.md` | M | +35 |

## AES proof-point (`≥30 % LoC reduction`) — N/A, parallel-track-owned

The brief asked for a rewrite of `lib/common/crypto/aes/round.spl`
showing ≥30 % LoC reduction. That path doesn't exist; the canonical
AES module is `src/lib/common/aes/{cipher,key_expansion,utilities,
modes,sbox,types,padding}.spl` (1,331 LoC total).

Searched all 7 files for byte-extraction patterns
(`<< 24|<< 16|<< 8|>> 24|>> 16|>> 8|0xFF000000|0xFF0000|0xFF00`):

```
$ grep -nE '<<\\s*24|>>\\s*24|0xFF000000' src/lib/common/aes/*.spl
(no output)
```

`src/lib/common/aes/` stores AES state as a 16-byte `[u8]` list (per
`state_get(state, row, col)` in `cipher.spl`), not packed u32 words —
so there are no `& 0xFF000000 >> 24` chains to rewrite. This matches
the earlier commit's recorded judgment:

> AES rewrite (≥30% LoC reduction acceptance gate): N/A. The AES
> implementation under src/lib/common/aes/ stores state as a 16-byte
> list (`state_get(state, row, col)`), not packed u32 words, so there
> are no `& 0xFF000000 >> 24` shift+mask chains to rewrite. Recorded
> here so future readers see the gate was confirmed inapplicable, not
> skipped.

The packed-u32 byte-extraction chains DO exist in
`src/os/crypto/aes_gcm.spl` (lines 76, 80, 106-108, 241-243, 439-449,
468-475) and `src/os/crypto/aes128_gcm.spl` (lines 76-80, 122-124,
405-415, 427-440). Per the C-1 brief disjoint-scope rules:

> Do NOT touch: ... Other crypto modules — they're being migrated
> by parallel tracks.

`src/os/crypto/*.spl` is parallel-track territory; rewriting them
here would race with M-A / M-B / M-C / P-1. The proof point is
deferred to whichever track owns those files when they ship the
crypto port. **Per the brief, the AES gate is documented-N/A here
and not blocking.**

## Verification

### `bin/simple test --clean` on the spec

```
$ bin/simple test --clean test/unit/compiler/bitfield_sugar_spec.spl
Files: 1
Passed: 15
Failed: 0
```

### Deliberate-fail probe — INCONCLUSIVE (pre-existing infra)

Per `feedback_compile_mode_false_greens.md` and the B3 R2-broader
note in `compiler_bugs_for_crypto_2026-04-25.md`:

> --mode=native runs ... stubs.rs which prints "Generating 234 stub
> functions for unresolved symbols" and replaces every std.spec call
> with a no-op stub. The "PASSED" is meaningless.

I ran a deliberate-fail probe both on the real spec (flipped one
expected value 0x78 → 0x99, restored after) and on a tiny
`expect(1).to_equal(2)` spec at `/tmp/b4probe/min_fail_spec.spl`.
**Both reported PASSED.** This confirms the test runner is in a
false-green mode for this kind of spec — `expect()` matchers aren't
asserting, regardless of B4-sugar correctness. **Not a B4 bug;
infra-level issue per memory.**

### Behavioral probe — runtime crash, also pre-existing

`bin/simple interpret /tmp/b4probe/probe_main.spl` segfaults with
`malloc_consolidate(): invalid chunk size` (exit 134). `bin/simple
<file>` and `bin/simple run <file>` exit 248 silently. Plain
`bin/simple -c 'println(1+2)'` also doesn't reach output. The
runtime is broken in this checkout for ad-hoc scripts; the test
runner subcommand is the only working entry point. Behavioral
verification of the sugar is gated on whoever fixes the runtime.

The fact that `simple-parser` cargo unit tests (206/206 PASS per the
earlier commit message) and `compile_smoke_spec` (2/2 PASS) covered
the implementation is the strongest signal we have that the sugar
itself is correct.

### File-hash invariant

Restored bitfield_sugar_spec.spl after the deliberate-fail probe;
md5 matches original (`f116e234d33ee1eec7b5c7f86d8c53c7`).

## Bootstrap rebuild — NOT needed

Per memory `feedback_extern_bootstrap_rebuild.md`: bootstrap rebuild
is required only when adding a new `rt_*` extern. B4-sugar adds
**no new externs** — it's a pure parser rewrite into existing binary
operators. The Rust-seed compile is the only build step required,
and that already happened on the commits that landed this work.

## `advisor()` interactions

1. Pre-implementation: advisor recommended **parse-time AST-shape
   desugar** over a new EXPR variant ("collection_desugar precedent").
   Result: matches what `main` already shipped — implementation
   already chose the recommended approach.

2. Post-deliberate-fail-probe: advisor diagnosed false-green as
   pre-existing infra (`feedback_compile_mode_false_greens.md`),
   and pointed out the spec docstring already specified inline
   binary lowering rather than helper-call lowering. Both points
   matched what `main` actually shipped.

3. Pre-done-doc: not consulted — the substantive question (AES
   proof point) was settled by the disjoint-scope rule, not by
   judgment.

## Why no compiler edit by C-1

The brief said: "If a self-hosted-only sugar can be implemented
without Rust changes, do so." The sugar is a parser-level rewrite;
the self-hosted path delegates parsing to the Rust seed (no separate
self-hosted parser exists today). Therefore implementing in pure
Simple wasn't possible, and `main` already had the Rust-seed
implementation. Re-implementing it would have been a no-op or
worse — a duplicate that loses the in-tree work.

## Files I did NOT touch (per disjoint-scope discipline)

- `src/compiler_rust/**` — owned by I-2 / I-6 / C-2 (already
  contains the B4 work)
- `src/lib/common/math/{bignum,field}/**`,
  `src/lib/common/integer_serde.spl` — I-3 / I-4 / I-5 / M-A / M-B /
  M-C / P-1
- `src/os/apps/sshd/*.spl`, `src/lib/common/runtime_symbols.spl`,
  `src/lib/common/bitwise_utils.spl`
- `src/os/crypto/*.spl` — parallel-track migration
- `src/lib/common/aes/*.spl` — AES module owner
