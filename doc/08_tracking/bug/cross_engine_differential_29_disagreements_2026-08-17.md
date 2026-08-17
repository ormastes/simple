# Cross-engine differential: 29 of 150 cells disagree between interpreter and JIT

**Filed:** 2026-08-17
**Severity:** HIGH — silent wrong results, no diagnostic on any of them
**Found by:** `scripts/check/check-engine-differential.shs` on first run
**Status:** RESOLVED for 28 of 29 cells; **ONE still live** — see the update
below, which is the actionable part of this document.

---

## UPDATE (same day): re-run on a freshly built compiler — 28 of 29 were
## already fixed in-tree, ONE survives

The original run used the deployed `bin/simple`, a Rust seed whose mtime
(2026-08-16 22:59) predates most of 2026-08-17's fixes. Rebuilding from the
current tree into an isolated `CARGO_TARGET_DIR=/mnt/data/cargo-target-failopen`
and re-running the identical probe:

    fresh binary: 59402304 bytes, Aug 17 06:18
    interpreter: 150 observations
    jit:         150 observations    (was 149 — the dropped observation is fixed)
    DISAGREEMENTS: 1

| cell | interpreter | jit |
|---|---|---|
| `copy_arr_u8_copy` | 2 | 99 |

**Everything in sections A, B, C and D below is already fixed in-tree and was
merely not yet deployed.** That includes the whole divide-by-8 nullable family,
every raw-tagged-word rendering, every `nil`-swallowed payload, the dropped
`opt_bang_text` observation, and all five f32 struct-field cells. This document
keeps them recorded because they are the calibration evidence that the gate
detects real defects rather than noise — but no action is needed on them beyond
redeploying the compiler.

**The single live defect is section E: `[u8]` copy aliasing on the JIT only.**

    var src: [u8] = [1, 2, 3]
    val cp = src        # must be a copy
    src[1] = 99
    # interpreter: cp[1] == 2   (correct — `val cp = src` did not alias)
    # JIT:         cp[1] == 99  (wrong — the copy aliases the source buffer)

This is worth separating from the standing note that `[u8]` "is KNOWN to still
alias". That note describes a uniform language-level limitation. What the probe
shows is narrower and worse: the two engines DISAGREE about it, so the same
source has different value semantics depending on how it is executed. The
sibling cells `[i64]`, `[u64]`, `[f64]` and `[text]` all copy correctly on both
engines, so this is specific to the packed byte-array representation in the
JIT, not to array copying in general.

Not fixed here: this lane owns the detector, not the codegen.

---

**Original run (deployed seed), retained as calibration evidence:**

## What was run

`test/01_unit/compiler/codegen/probe_engine_differential.spl` — one
deterministic program, 150 observations, executed under
`SIMPLE_EXECUTION_MODE=interpreter` and `=jit`. The probe carries no expected
values at all; the only assertion is that two implementations of one language
must not DISAGREE. That is deliberate: every codegen defect found on
2026-08-17 shipped because nobody knew the right answer for one particular
cell, so a harness that requires knowing the right answer cannot catch the
next one.

**Binary under test:** `bin/simple` ->
`bin/release/x86_64-unknown-linux-gnu/simple`, the deployed RUST SEED, mtime
2026-08-16 22:59. This PREDATES most of 2026-08-17's fixes, so an unknown
share of the list below is already fixed in-tree and merely not yet deployed.
Separating the two requires re-running against a freshly built compiler; see
"What was NOT proved".

## Result

    interpreter: 150 observations
    jit:         149 observations   <-- one observation never printed
    29 cells disagree

The count mismatch alone is a finding: the JIT dropped `opt_bang_text`
entirely rather than printing a wrong value.

## The disagreements, grouped by shape

### A. Sub-64-bit nullable payloads are divided by 8 (NEW as a generalisation)

| cell | interpreter | jit | ratio |
|---|---|---|---|
| `opt_bind_i32` | 70000 | 8750 | /8 |
| `opt_bind_u16` | 60000 | 7500 | /8 |
| `opt_bind_u32` | 4000000000 | 500000000 | /8 |
| `opt_bind_u8`  | 200 | 25 | /8 |

Exactly /8 in all four. The `[u64]` divide-by-8 stride defect was known for
ARRAY elements; the array cells in this probe (`arr_u64_*`, `arr_u8_*`,
`arr_i32_*` …) all AGREE, so that path appears fixed. The same divide-by-8
appears here on a completely different path — a scalar bound into a nullable
`T?` slot. This generalisation does not appear to have been recorded.

### B. Nullable payloads rendered as raw tagged words

| cell | interpreter | jit |
|---|---|---|
| `opt_bind_i16` | 300 | `<value:0x12c>` |
| `opt_bind_u64` | 4294967297 | `<invalid-heap:0x100000001>` |
| `opt_coalesce_default_i64` | 9 | `<invalid-heap:0x9>` |
| `opt_return_i64` | 7 | `<value:0x7>` |
| `opt_return_nil_coalesce` | 55 | `<value:0x37>` |
| `opt_bind_i64` | 42 | 2e-322 (the known TAG_FLOAT re-read) |
| `opt_coalesce_present_i64` | 42 | 2e-322 |
| `opt_return_f64` | 2.5 | 576601489791778816 |

Same family as
`doc/08_tracking/bug/jit_optional_i64_payload_reinterpreted_2026-08-17.md`,
but across many more types than that bug records.

### C. Nullable payloads that vanish into `nil` or `0`

| cell | interpreter | jit |
|---|---|---|
| `opt_bind_i8` | 3 | nil |
| `opt_bind_bool` / `opt_bang_bool` | true | nil |
| `opt_coalesce_default_bool` | true | nil |
| `opt_bang_i64` | 42 | nil |
| `opt_bang_f64` | 2.5 | nil |
| `opt_bang_text` | ok | **absent — never printed** |
| `opt_bind_f32` / `opt_bind_f64` | 1.5 / 2.5 | 0 |
| `opt_coalesce_present_f64` | 2.5 | 0 |
| `opt_coalesce_default_f64` | 9.5 | 0 |

`!` returning `nil` is the worst cell here: the unwrap operator is exactly
where a caller believes the value is present.

### D. f32 struct fields read as 0.0 (known bug, still live in the deployed seed)

`inline_field_f32`, `retval_field_f32`, `retval_direct_field_f32`,
`write_field_f32`, `array_widths_f32` — all 1.5/7.5 on the interpreter, 0.0 on
the JIT. Matches
`doc/08_tracking/bug/f32_struct_field_reads_as_zero_2026-08-17.md`. Worth
noting the probe finds it on FOUR distinct receiver forms (inline-built,
returned-by-value with and without an intermediate binding, after a field
write, and out of an array), where the original bug recorded one.

### E. `[u8]` copy semantics differ BETWEEN ENGINES (NEW)

| cell | interpreter | jit |
|---|---|---|
| `copy_arr_u8_copy` | 2 | 99 |

`val cp = src; src[1] = 99` — the copy reads 2 on the interpreter and 99 on
the JIT. The known note is that `[u8]` "still aliases"; what is new here is
that it aliases on ONE engine only. `[i64]`, `[u64]`, `[f64]` and `[text]`
copies agree and are correct on both, so this is specific to the packed
byte-array representation in the JIT.

## What AGREED (121 of 150 cells)

Recorded because agreement is evidence too, and because it bounds the blast
radius:

- every plain scalar local and all arithmetic (i8/i16/i32/i64/u8/u16/u32/u64/
  f32/f64/bool/text)
- **the whole access.rs by-value struct return shape** — `retval_w3_first`,
  `retval_w3_length`, `retval_w3_tag` and their no-intermediate-binding forms
  all agree at 9/3/77. The field-0 collapse does NOT reproduce on the deployed
  seed for i64 fields; only the f32 field of the same struct is wrong.
- all nested struct reads, all struct field writes and their neighbours
- all tuple reads, direct and returned
- every array element read and write, INCLUDING packed `[u64]` and `[u8]`, and
  their neighbours — the array-side divide-by-8 appears fixed
- struct copy semantics, by-value argument passing, and `[i64]`/`[u64]`/
  `[f64]`/`[text]` array copies

## What was NOT proved

- **Native/AOT.** The third engine did not complete within this session's
  budget for the 150-observation probe (`native-build` succeeded on a trivial
  probe, so the lane works; the large probe was still building). Every verdict
  above is interpreter-vs-JIT only. The gate refuses to call a 2-engine run a
  3-engine one: `--quick` records that fact in the verdict, and a native lane
  that fails to build is a FAIL, never a skip.
- ~~Which of these are already fixed in-tree.~~ **Answered by the UPDATE at the
  top of this document: 28 of 29 were already fixed, 1 is live.**
- **Root cause of any individual cell.** This lane detects disagreement; it
  does not localise it. In particular `access.rs` is owned by another lane and
  was not touched.

## Reproduce

    sh scripts/check/check-engine-differential.shs --quick
    SIMPLE_BIN=/path/to/fresh/simple sh scripts/check/check-engine-differential.shs
