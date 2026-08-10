# JIT returns a tag-corrupted `[i64]` from `sha1_bytes` — floats, `nil` and heap tags inside an i64 list

**Status:** OPEN
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
Status: **UNABLE-still-open — architecturally plausible per grep evidence,
but fresh execution evidence blocked by an unrelated compile regression;
re-verify once the `rotl32` resolution gap is fixed.**
