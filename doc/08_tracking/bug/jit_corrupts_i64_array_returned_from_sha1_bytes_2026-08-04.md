# JIT returns a tag-corrupted `[i64]` from `sha1_bytes` — floats, `nil` and heap tags inside an i64 list

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-04

## Symptom

`build/tmp_gap/sha1chk.spl` (run from the repo root — an absolute path makes
`simple run` exit 0 without compiling):

```simple
use std.common.crypto.sha1.{sha1_bytes}

fn main():
    val abc: [i64] = [97, 98, 99]           # "abc"
    print("raw_sha1abc={sha1_bytes(abc)}")
```

```
$ SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpret bin/simple run build/tmp_gap/sha1chk.spl
raw_sha1abc=[169, 153, 62, 54, 71, 6, 129, 106, 186, 62, 37, 113, 120, 80, 194, 108, 156, 208, 216, 157]
        # == a9993e364706816aba3e25717850c26c9cd0d89d — the RFC 3174 value for SHA-1("abc"). CORRECT.

$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple run build/tmp_gap/sha1chk.spl
raw_sha1abc=[<special:14>, 0.000…474, <special:6>, 14, <value:0xf7>, <value:0x54>,
             <invalid-heap:0xc1>, 5, <value:0x64>, nil, <value:0x3e>, 23, 0.000…395,
             26, <value:0x34>, 20, <value:0x7f>, 26, <value:0xfd>, 10]
```

Exit 0, no warning, no error. A declared `[i64]` comes back holding `nil`, two
denormal floats, an `<invalid-heap:…>` pointer and several `<special:N>` /
`<value:0xNN>` tag markers. Rendered as hex it produces
`7362330ef754c10564033e17521a34147f1afd0a` — a plausible-looking 40-hex-digit
digest that is simply wrong.

The same divergence hits `hmac_sha1_bytes` (RFC 2202 test case 1 returns
`0254230599fe1c07…` on the JIT instead of `b617318655057264…`), which is
consistent with HMAC being built on `sha1_bytes`.

## Root cause

Not yet isolated. The library is provably innocent: identical source, identical
input, correct on the tree-walk interpreter and corrupt on the Cranelift JIT, so
the fault is in the JIT's handling of the `[i64]` (`list`) value returned by
`sha1_bytes`. Note `sha1_bytes` is declared `fn sha1_bytes(bytes: list) -> list`
(`src/lib/common/crypto/sha1.spl:252`) — an *untyped* `list`, not `[i64]` — so
the returned elements carry no static element type and the JIT appears to be
reading raw tagged words as if they were already-untagged i64s. That matches the
observed output exactly: each slot renders as whatever its tag says (float,
nil, heap pointer, special) rather than as an integer.

## Blast radius / why this matters

This is a false-green generator for the entire crypto lane. `bin/simple test`
runs specs on the **interpreter**, where these functions are correct, so every
SHA-1/HMAC-SHA-1/PBKDF2-SHA-1/SCRAM-SHA-1 spec is green — while any *program*
(`bin/simple run`, the JIT, which is what ordinary code uses) computing a SHA-1
digest gets silent garbage. The specs cannot see it by construction.

It is also a measurement trap for anyone verifying crypto by probe: a probe
written as `bin/simple run probe.spl` will report a wrong digest and make a
*correct* library look broken. That happened in this lane — a newly added
`pbkdf2_sha1_bytes` was first judged wrong on a JIT probe, then verified exactly
against RFC 6070 vectors 1 and 2 once the probe was re-run with
`SIMPLE_EXECUTION_MODE=interpret`.

Secondary finding from the same probe: `"abc"[i].to_i32()` returns **0** for
every index under the JIT, so any `bytes_of(text)` helper written that way
silently yields an all-zero byte array. That is consistent with
`doc/08_tracking/bug/jit_substring_chained_to_int_returns_pointer_2026-08-04.md`
(the `numeric_cast_target` no-op arm at
`src/compiler_rust/compiler/src/codegen/instr/methods.rs:131`) and is a second
reason JIT-side crypto probes cannot be trusted.

## Why not fixed now

The fix is in the Rust seed's Cranelift codegen (list element boxing/unboxing
across a call boundary when the callee's return type is the untyped `list`),
which is out of the pure-Simple lane and needs a full seed rebuild plus a
regression sweep over every `list`-returning intrinsic. Widening
`sha1_bytes`'s signature from `list` to `[i64]` is a plausible *narrow*
mitigation and should be tried first, but it must be validated on both engines
before it is claimed — an untested signature change here would just move the
corruption.

## Re-investigated 2026-08-10 (correcting a prior blanket-claim mislabel)

A prior pass in this session had mass-relabeled this doc using the incorrect
claim "the interpreter/JIT is implemented entirely under
`src/compiler_rust/**`, off-limits" as a blanket rule. Checked specifically
for THIS bug rather than assuming the blanket claim:

- `/usr/bin/grep -n "numeric_cast_target"
  src/compiler_rust/compiler/src/codegen/instr/methods.rs` — hits at lines
  117 and 130, confirming the doc's secondary-finding citation
  (`methods.rs:131`, off by one line vs. the `if let Some(to_ty) =` check at
  130 — close enough to be the same construct) is real and current. This is
  Cranelift-specific codegen (`src/compiler_rust/compiler/src/codegen/`),
  genuinely off-limits, not the tree-walk interpreter.
- Attempted to re-run the exact repro
  (`build/tmp_gap/sha1chk.spl` via `use std.common.crypto.sha1.{sha1_bytes}`)
  against the current source tree: it **no longer compiles** —
  `error[E1002]: function 'rotl32' not found`, even though
  `src/lib/common/crypto/types.spl:110` still defines `fn rotl32(...)`. This
  is an unrelated regression (a resolution/export gap unrelated to the JIT
  list-tagging bug this doc is about) that blocks a fresh end-to-end repro of
  the ORIGINAL bug this pass. Did not chase the `rotl32` resolution failure
  further — out of scope for this doc.
- Because the original repro path is currently blocked by this unrelated
  compile error, I could not re-confirm the exact JIT-corrupted-list output
  today. The root-cause attribution (Cranelift codegen boxing/unboxing of
  untyped `list` returns) is still grep-backed via the `numeric_cast_target`
  citation above, but the top-level symptom itself is **unconfirmed this
  pass**.

Conclusion: root-cause attribution to `src/compiler_rust/compiler/src/codegen/**`
remains grep-supported and was not the product of a blanket assumption.
However the original end-to-end repro could not be re-run today due to an
unrelated `rotl32` resolution regression in `sha1.spl`'s import chain.
Status (superseded below): **UNABLE-still-open — architecturally plausible per
grep evidence, but fresh execution evidence blocked by an unrelated compile
regression; re-verify once the `rotl32` resolution gap is fixed.**

## Re-investigated 2026-08-10 — repro unblocked, root cause re-confirmed with fresh execution evidence

Root-caused the `rotl32` resolution gap: `src/lib/common/crypto/sha1.spl`
imported `crypto.types` via the bare `mod crypto.types` form (also used by
`sha256_core.spl`, `sha3.spl`, `tls12_prf.spl`), which does not bring
unqualified names like `rotl32` into scope. The sibling `sha256.spl` uses the
working explicit form `use std.common.crypto.types.{rotr32}`. Fixed
`sha1.spl` to match:

```
- mod crypto.types
+ use std.common.crypto.types.{rotl32}
```

With that one-line fix, `rotl32` resolves and the exact original repro from
this doc now runs end-to-end again:

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run sha1chk.spl
raw_sha1abc=[169, 153, 62, 54, 71, 6, 129, 106, 186, 62, 37, 113, 120, 80, 194, 108, 156, 208, 216, 157]
# == a9993e364706816aba3e25717850c26c9cd0d89d — RFC 3174 SHA-1("abc"). CORRECT.

$ bin/simple run sha1chk.spl        # default JIT-first path
[jit-fallback] unresolved external symbol 'rotl32': whole module dropped to the interpreter
raw_sha1abc=[<value:0xfd>, <value:0x87>, 0.0, <value:0x95>, <value:0x7>, <value:0xf>,
             <value:0x7>, <special:27>, <value:0x1c>, <value:0x8d>, <value:0x17>,
             <invalid-heap:0x29>, <value:0x5>, <value:0x97>, <value:0xc4>, <value:0x3c>,
             <value:0x97>, <value:0xbe>, <value:0xe7>, <value:0x3c>]
```

This confirms the doc's original symptom is real and current: the default
JIT-first path (which now itself reports `unresolved external symbol
'rotl32'` and falls back to the interpreter for the *whole module*, yet the
returned `list` value is still tag-corrupted afterward) produces garbage from
the same source that the interpreter computes correctly. The corruption
persists even though the module fell back to the interpreter, consistent with
the doc's root-cause theory: the corruption is in how the JIT-compiled
**caller** (`main`, which called into a module that got interpreter-fallback)
unboxes an untyped `list` return value across the JIT/interpreter boundary —
this is `src/compiler_rust/compiler/src/codegen/**` (Cranelift JIT codegen /
FFI boundary), which is out of scope for a pure-Simple fix and requires a
Rust-seed change plus a full seed rebuild to fix properly.

**Status: ARCHITECTURAL-OPEN.** The blocking `rotl32` resolution regression
is FIXED (`src/lib/common/crypto/sha1.spl`, landed this pass — see commit
SHA in the fix-log below). The underlying JIT list-tag-corruption bug is
re-confirmed with fresh execution evidence and remains a genuine Cranelift
codegen defect in `src/compiler_rust/compiler/src/codegen/**`, which per this
task's hard constraints must not be edited here. A narrow pure-Simple
mitigation (widening `sha1_bytes`'s return type from untyped `list` to
`[i64]`) was proposed in the original doc but not yet attempted this pass;
left for a follow-up since it changes a public stdlib signature and needs
validation on both engines before landing.

---

## RE-MEASURED 2026-08-17 — still OPEN, but the symptom has CHANGED

`bin/simple` = Rust seed, `readlink -f bin/simple` =
`bin/release/x86_64-unknown-linux-gnu/simple`.

```
$ SIMPLE_EXECUTION_MODE=jit bin/simple run sha1chk.spl
[238, 108, 70, 110, 94, 234, 152, 37, 44, 128, 103, 215, 170, 90, 6, 148, 47, 250, 31, 170]
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run sha1chk.spl
[169, 153, 62, 54, 71, 6, 129, 106, 186, 62, 37, 113, 120, 80, 194, 108, 156, 208, 216, 157]   # RFC 3174, correct
```

**The tag corruption in the RETURNED digest is gone** — no `<special:N>`, no
`nil`, no `<invalid-heap:…>`, no denormal floats in the final list. What remains
is a plain **wrong digest**: 20 clean integers, all wrong. So the "JIT reads raw
tagged words as untagged i64s *when returning a `list`*" hypothesis in the
original Root cause section is **no longer supported by the evidence** and
should not be used to drive a fix.

### Bisected — where the divergence actually starts

| stage | JIT vs interpreter |
|---|---|
| `sha1_pad_message([97,98,99])` | **identical** (64 bytes, `…, 0, 24`) |
| message schedule `w[0..15]` | **identical** (`[1633837952, 0 x14, 24]`) |
| `rotl32`, `add_mod32`, `sha1_f(t,…)` for t=0/20/40/60, `sha1_k(t)` | **identical** in isolation |
| `w[16]` (first extended word) | **DIVERGES** — JIT `371603456`, interpreter `3267675904` (= `rotl32(0x61626380,1)` = `0xC2C4C700`, correct) |
| `sha1_process_block(initial_h, block)` | JIT `[4000073326, 1592432677, 746612695, 2858026644, 804921258]` vs interpreter `[2845392438, …]` (= `a9993e36…`, correct) |

Reproduces in a standalone copy of `sha1_process_block` in a scratch file, so it
is not a `use`/module-resolution artifact and the library is again confirmed
innocent.

**Tag corruption IS still present, just later:** printing the working variable
`a` after each of the first three rounds yields a denormal float and a
`<value:0x57cfa1df>` on the JIT.

### What could NOT be narrowed further (be honest about this)

Every attempt to reduce `w[16]` to a standalone reproducer **agreed on both
engines**, including: the raw xor chain over `.get()`s; `rotl32` of that chain
inline inside a `push`; the same with the real `0x61626380` value; growing an
array literal past its initial capacity of 16 while reading it. The divergence
so far only appears in the full ~80-iteration loop, and the mechanism is
**UNPROVEN**. Do not close this on the old hypothesis.

### A related, newly proven defect in the same family

`doc/08_tracking/bug/jit_tuple_get_returns_raw_tagged_word_to_i64_sink_2026-08-17.md`
— `tuple.get(i)` delivers a raw `TAG_INT` word (`v << 3`) to any `i64`-typed
sink under the JIT, so `(5,6).get(0)` binds as `40`. That IS "a raw tagged word
read as if already untagged", it is minimal, and `sha1`'s context type is
`(list, list, i64, i64)` read via `ctx.get(2)` / `ctx.get(3)`. It is a strong
candidate contributor here and is filed separately with a 5-line reproducer.
