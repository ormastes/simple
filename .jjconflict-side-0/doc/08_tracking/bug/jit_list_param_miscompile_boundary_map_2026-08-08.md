# JIT tagged-element miscompile — independent boundary map (adversarial re-take)

Status: DUPLICATE of jit_param_passed_list_element_read_returns_tagged_2026-08-08.md
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Date:** 2026-08-08 · **Verifier:** adversarial review lane · **Engine:** JIT
(Cranelift) via `bin/simple run` on the Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple`.
**Companion to** `jit_param_passed_list_element_read_returns_tagged_2026-08-08.md`,
whose core claim is **CONFIRMED** and whose boundary is **WIDER than filed**.

Probes: `build/jitprobe/srcA/main.spl`, `probeB.spl`, `probeC.spl`, `probeD.spl`.
Every row below was run on **both** the JIT lane and
`SIMPLE_EXECUTION_MODE=interpret`. **The interpreter is correct on every single
row.** All probes are standalone (no `use`), so the bundled-stdlib cwd trap
recorded in the original filing cannot apply.

## The rule (this is the load-bearing result)

> **Corruption is decided by the CALLEE's declared parameter type, not by the
> caller's, and not by the value.**

Proved by row A13: the caller declares `var e2: [i64]`, the callee still declares
`data: list` → **still corrupt (84)**. So a correctly-typed caller cannot protect
a `list`-typed callee, and the at-risk set is exactly "functions declaring a
`list`/`list<T>`/untyped parameter that then read elements" — a **callee-side,
greppable** set. This is what makes the sweep below sound.

| declared param type | element read | verdict |
|---|---|---|
| `data: list` | tagged (`v<<3`) | **CORRUPT** |
| `data: list<i64>` | tagged | **CORRUPT** (new — not in the filing) |
| untyped `data` | tagged | **CORRUPT** |
| `data: [i64]` | correct | safe |
| `data: [u8]` | correct | safe |
| `data: [i32]` | correct | safe |
| local list built inside the fn | correct | safe |
| inline in `main` | correct | safe |

`list<i64>` being corrupt is important: naming the element type in **generic**
form does **not** protect you. Only the `[T]` bracket-array form does.

## Rows the original filing did NOT cover

| # | form | JIT | interp / truth | verdict |
|---|---|---|---|---|
| A09 | `for x in data` over a `list` param | **56** | 7 | **CORRUPT — iteration, not just indexing** |
| A05/A06/A07 | `data.len()` on a `list` param | 996 | 996 | **safe** (length is NOT tagged) |
| A14 | `data[3] = 5` in callee, read in caller | 5 | 5 | **safe** (writes are correct) |
| A08 | `data[3] == 2` (literal) | true | true | **accidentally right** |
| B10 | `data[3] > other` (**variable**) | **1** | 0 | **CORRUPT** |
| A12 | element extracted then passed onward | 84 | 98 | corrupt, but **no double-tagging** (stays `v<<3`) |
| C03/C04 | two-hop through another `list` fn | 84 | 98 | corrupt, propagates |
| C05/C06 | nested `rows[0][1]` | 84 | 98 | corrupt |
| B06/B07/B08 | `*10` / `/2` / `%3` on element | 160 / 8 / 1 | 20 / 1 / 2 | corrupt in every arithmetic op |
| B09 | index by a variable rather than a literal | 84 | 98 | corrupt |

**The two biggest additions are A09 and B10.**

- **A09 — `for x in data` is corrupt too.** The filing only covered `data[i]`.
  Iteration is the far more common idiom, so the real blast radius is larger
  than filed. Any accumulate-over-a-list-param helper is wrong by 8×.
- **B10 — comparison against a *variable* is wrong.** The filing's summary says
  the value "compares correctly against small literals", which is true (A08) but
  reads as reassurance. It is only literal comparisons that are accidentally
  right; `data[i] > n` for a variable `n` is **silently wrong**, and that is the
  shape used in every bounds check and every sort/compare helper.

**Correction to the filing:** `data.len()` is safe. The filing left this
untested; a tagged length would have been catastrophic, and it is worth
recording as a negative result so nobody re-tests it.

## `.at()` and `.get()` are SEPARATE defects, not this one

The filing folded `.at(3)` into the same root cause. It is not the same:

- `data.at(3)` → `-6237607107837` — a **raw word**, not `v<<3`. Different
  lowering defect; needs its own filing.
- `100 - data.get(3)` → the **interpreter rejects this outright**
  (`semantic: type mismatch: cannot convert enum to int`, because `.get` returns
  an Option) while the **JIT silently accepts it and yields 84**. The verified
  claim is the *divergence*: one engine treats this as a type error, the other
  compiles it and returns a value. The mechanism is not established — since 84
  is identical to plain indexing, the JIT may simply be lowering `.get` to an
  index rather than doing arithmetic on an Option. Either way it is a
  front-end/type-safety divergence separate from the tag bug.

So "the boundary" is **three** defects sharing one symptom surface, not one.

## Victim sweep (the at-risk set, measured)

Against `origin/main`, `.spl` only, via `/usr/bin/grep`:

- **1,356** function declarations take a `list` / `list<T>` parameter, across
  **180** files.
- Narrowing to those that **index or iterate that parameter AND do arithmetic on
  the element, or compare it against a variable**: **49 sites**.

  *Methodology note, because the first version of this sweep was wrong.* The
  scanner initially skipped any function that never wrote `param[`, which would
  have discarded every **iterate-only** function — exactly the A09 idiom proved
  corrupt above. That gate was removed and the sweep re-run. The count did
  **not** move: still 49. A positive control confirms this is a real negative
  and not a dead detector — a synthetic `for x in data: s = s + x` body is
  correctly flagged by the iteration matcher. The kind distribution over the 49
  is **46 arithmetic-on-index, 3 compare-against-variable, 0 iterate-only**:
  in this corpus, functions that iterate a `list` parameter essentially always
  index it as well. So 49 is a real count for this shape, not a floor —
  though it remains a *lower* bound in the sense that any purely textual
  scanner under-counts dynamic and aliased uses.
- Those 49 are **not** evenly spread. By area: **37 in `src/os/`, 12 in
  `src/lib/`** — and they are overwhelmingly **cryptographic bignum arithmetic**:
  - `src/lib/common/crypto/rsa_pkcs1.spl` — `_p_add`, `_p_sub`, `_p_mul`,
    `_p_mul_i64`, `_p_divmod_i64`, `_p_get_bit`, `_p_shift_left_one`, `_p_compare`
  - `src/os/crypto/curve25519_bigint.spl` — `_bi_add`, `_bi_sub`, `_bi_mul`,
    `_bi_mul_i64`, `_bi_divmod_i64`, `_bigint_low_255`
  - `src/os/crypto/ed448.spl` — the same `_bi_*` family
  - `src/lib/common/aes/utilities.spl` — `compute_checksum`, `blocks_equal`

**Spot-check, executed.** `build/jitprobe/probeD.spl` is a faithful standalone
copy of `rsa_pkcs1.spl:83 _p_add` (origin/main). Adding limb vectors `[1,2]` and
`[3,4]`:

| lane | result | truth |
|---|---|---|
| JIT | `[32, 48]` | — |
| interpreter | `[4, 6]` | `[4, 6]` |

Exactly 8×. **The pure-Simple RSA / Curve25519 / Ed448 bignum layer computes
wrong answers on the JIT lane**, and `bin/simple test` cannot see it because the
spec suite runs the interpreter, which is correct.

`_p_compare` is *accidentally* safe: it compares two elements that are **both**
tagged, so the factor cancels. That is luck, not correctness — it breaks the
moment one side is a plain integer.

## Why the spec suite is blind

`bin/simple test` runs the interpreter. Every row above is correct there. So
there is **no spec that can fail** on any of this, and none of these 49 sites can
be protected by a spec. A fence for this belongs in `scripts/check/`, not in a
spec — consistent with the standing finding that AOT/JIT-lane defects are
invisible to the spec corpus.

## Pure-Simple codegen — SETTLED, and it is CLEAN

This was the filing's explicitly untested half. It is now measured.

Probe `build/jitprobe/srcE/main.spl` — `fn n_list(data: list) -> i64: 150 - data[3]`,
`main` returns it as the process exit code (no interpolation, no `use`, so no
stdlib is needed and the bundled-stdlib trap cannot apply):

| lane | exit code | truth = 148 | verdict |
|---|---|---|---|
| **pure-Simple `native-build`** | **148** | 148 | **CORRECT** |
| JIT (`bin/simple run`, same file, same run) | **134** | 148 | corrupt (`150-16`) |

Built with a **bare positional** `.spl` argument, never `--entry` (which
delegates to `run_rt_native_build`, the Rust runtime, and would have
re-measured the seed).

Two falsification checks, both required before believing this:

1. **Positive capability.** Editing the source `100` → `150` moved the built
   binary's answer `98` → `148`. The artifact tracks the source; it is not a
   stale cached build.
2. **Provenance.** `rt_enum_check_discriminant` — the symbol emitted only by
   `src/compiler_rust/**` — occurs **0** times in the output binary. This is not
   Rust-seed codegen.

**Conclusion, stated no wider than the evidence.** This experiment varied *two*
things at once — compiler (seed vs pure-Simple) and lane (JIT vs AOT) — so the
precise result is:

| | JIT lane | AOT / native-build | interpreter |
|---|---|---|---|
| **seed** (`bin/simple`) | **CORRUPT** | n/a | correct |
| **pure-Simple** | **UNTESTED** | **correct** | correct |

- The **seed's Cranelift JIT is corrupt**.
- The **pure-Simple AOT/native-build path is clean**.
- The **pure-Simple JIT path is UNTESTED**, and cannot be tested here: the only
  deployed binary is the seed (`bin/release/x86_64-unknown-linux-gnu/simple`
  prints the bootstrap-seed banner), and no pure-Simple `simple` binary exists in
  this tree to run the probe through its own default non-`interpret` path.

So **do not** read this as "production is safe" in general. What is established
is that native-build output is safe. Whether the self-hosted compiler's JIT
shares the seed's lowering bug is an open question, and it is the question that
matters once the pure-Simple binary becomes the default tool. Re-run
`build/jitprobe/srcE/main.spl` through a deployed pure-Simple binary when one
exists; unblock condition is exit code 148.

## Two fail-open defects in `native-build` found while doing this

Both are separate small filings:

1. `bin/simple native-build --source <dir> -o <out>` (no entry) printed
   `Error: No entry point specified for native-build backend` and **still exited
   0**, producing no output binary. A caller checking only `$?` reads that as
   success.
2. A bare-positional build that scanned the default source roots ended with
   `error: native-build worker exited with code 1` and **also exited 0**. The
   scoped build correctly returned 1, so the fail-open is in the
   default-source-root path specifically.

Anything gating on `native-build`'s exit status should also assert the output
binary exists.
