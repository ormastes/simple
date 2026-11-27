# JIT: `tuple.get(i)` hands a RAW TAGGED word to an `i64` sink — `5` reads back as `40`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**ID:** jit_tuple_get_returns_raw_tagged_word_to_i64_sink_2026-08-17
**Date:** 2026-08-17
**Severity:** P1 — silent wrong value, exit 0, no diagnostic.
**Status:** FIXED (verified 2026-11-03, fix commit ee815637f72; see "Verified" at the end).
**2026-11-11 update:** a second lowering site of the same defect — tuple
*destructuring assignment* — is now also FIXED (see addendum at the end).

## How it was found

Not by looking for it. It was caught by the *similar-problem detection* probe
written for
`doc/08_tracking/bug/i8_array_literal_reads_back_wrong_value_2026-08-17.md`
(`test/01_unit/compiler/codegen/probe_int_width_boxing_matrix_jit.spl`), whose
`tuple_i64_0` row failed while the i8 reproducer it was generalising from said
nothing about tuples. That is the seventh time today a prevention spec caught a
defect its own reproducer missed.

## Reproduction (measured 2026-08-17, `bin/simple` = Rust seed)

```simple
fn takes(x: i64) -> i64:
    x

fn main():
    val t = (5, 6)
    val a: i64 = t.get(0)
    print a                 # JIT: 40    interpreter: 5
    print takes(t.get(0))   # JIT: 40    interpreter: 5
    print t.get(0) + 0      # JIT: 5     interpreter: 5   <- correct
    val l = [5, 6]
    print takes(l.get(0))   # JIT: 5     interpreter: 5   <- arrays are fine
```

```
$ SIMPLE_EXECUTION_MODE=jit bin/simple run tup3.spl
40
40
5
5
5
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run tup3.spl
5
5
5
5
5
```

`40 == 5 << 3`, i.e. the runtime TAG_INT word for 5 (`v << 3 | 0b000`) delivered
un-untagged. `print t.get(0)` on its own is CORRECT — the print path accepts a
tagged RuntimeValue — so the defect only shows when the erased `.get()` result
flows into a slot or parameter statically typed `i64`, which is exactly where no
unbox is emitted.

## Why this matters / relation to other rows

This is the same family as
`doc/08_tracking/bug/jit_corrupts_i64_array_returned_from_sha1_bytes_2026-08-04.md`
("a raw tagged word read as if it were already untagged"), but on the tuple
`.get()` path rather than the array one. Arrays are clean here; tuples are not.

Scale factor: `x8`. Any code that reads an i64 out of a tuple into a typed
binding gets a value eight times too large, silently. `.get()` on a tuple is the
idiomatic way this tree returns multi-value results (e.g. the whole
`(list, list, i64, i64)` streaming-hash context shape in
`src/lib/common/crypto/sha1.spl`).

## Not yet done

- Which lowering site omits the unbox (array `.get()` emits one, tuple `.get()`
  does not — the asymmetry is the lead).
- Whether `u64`/`i32` tuple sinks are affected: `tuple_u64_0` and `tuple_i32_0`
  PASS in the matrix probe, so this may be i64-specific, which would point at a
  "same machine width, therefore no conversion needed" shortcut.
- Whether struct fields and dict values share it.

## Detection

`test/01_unit/compiler/codegen/probe_int_width_boxing_matrix_jit.spl`, row
`tuple_i64_0`, asserted by
`test/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.spl`. That
spec is expected to be RED on this row until this bug is fixed; per
`.claude/rules/testing.md` the assertion is left in place rather than weakened.

## Re-verified STILL OPEN + the omitted lowering site is now identified (2026-08-17)

Binary identity:

```
$ readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59537240 2026-08-17 12:58:51.339525019 +0000     (the Rust seed, rebuilt 12:58)
```

Repro re-run verbatim (the record's own program):

```
$ SIMPLE_EXECUTION_MODE=jit bin/simple run r2.spl
40
40
5
5
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run r2.spl
5
5
5
5
```

**Answer to "which lowering site omits the unbox": there is no tuple site.**
This is a RUST SEED defect, in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`:

| line | arm | behaviour |
|---|---|---|
| 263 | `method == "get" && receiver_is_array(..)` | routes to `lower_index_expr(receiver, &args[0], element_ty)` — which pairs the read with `UnboxInt`/`UnboxFloat` (+`UnitNarrow`). CORRECT. |
| 290 | `method == "get" && receiver_is_dict(..)` | same routing. CORRECT. |
| — | tuple receiver | **absent.** No `receiver_is_tuple` arm exists. |

With no arm, a tuple `.get(i)` falls through to the generic dotted-name path and
lands on `codegen/instr/methods.rs:459-462`
(`("Tuple","get") => call_runtime_2(.., "rt_tuple_get", ..)`), which emits a bare
call and NO unbox. `rt_tuple_get`
(`src/compiler_rust/runtime/src/value/collections.rs:2214`) returns the tuple
slot verbatim — a tagged `RuntimeValue` — so an `i64`-typed sink receives
`v << 3`. Arrays escape this because `("Array","get")`
(`methods.rs:378`) is never reached: line 263 intercepts first.

`print t.get(0)` is correct for the same reason the record already gives: the
print path accepts a tagged RuntimeValue.

Fix shape (not applied — Rust seed, per this task's rules): add a
`receiver_is_tuple` arm alongside lines 263/290 that resolves the element type
from the tuple's HIR type at the (constant) index and routes through the same
unbox tail (`unbox_dict_read_result`, `lowering_expr_struct.rs:707`). Note the
element type is per-INDEX for a tuple, unlike array/dict, so the arm must
require a constant index and fall back to the current behaviour otherwise —
which is why this is not a copy-paste of the array arm and was not guessed here.

This also predicts the record's open question about `f64`/struct tuple sinks:
every non-`ANY` scalar sink is affected, and `u64`/`i32` "passing" in the matrix
probe is most likely those rows' sinks not being statically typed, not the
defect being i64-specific. Not measured; stated as a prediction, not a finding.


## Host-environment classification (2026-09-18)

Audited by the fix-pipeline classification review: **seed-owned** — seed-owned. This row is not executable on the macOS aarch64 host fix lane; it resumes when the blocking condition clears.

**Revalidated 2026-11-02: still plausible because OPEN — re-verified on the 2026-08-17 12:58 seed; the omitted lowering site is now identified (see the end of this record). Not fixed: Rust s; no merged fix commit with a passing regression is cited in this doc.**

## Verified (2026-11-03)

Fix commit `ee815637f72` (HIR + MIR constant-index tuple `.get()` typed unbox).
Verified on the current release/1.0.0 seed (`bin/simple.exe`, Rust seed):
the record's repro prints `5 5 5 5` under both `SIMPLE_EXECUTION_MODE=jit` and
`interpreter` (was `40 40 5 5` under jit), and
`test/01_unit/compiler/codegen/probe_int_width_boxing_matrix_jit.spl` prints
PASS for every row including `tuple_i64_0`, `tuple_inferred_i64_1`,
`tuple_mixed_i64_1`, `tuple_mixed_text_1`, `tuple_labeled_i64_1`,
`tuple_labeled_text_0`. (The `test` subcommand is unavailable on the seed, so
the probe was run directly via `run`.)

## Addendum 2026-11-11 (lane seedfix, routed from boot7 / PR #8193): destructuring-ASSIGNMENT site of the same defect — FIXED

The ee815637f72 fix typed only the constant-index `.get()` path. The OTHER
consumer of `rt_tuple_get` — the tuple-destructuring-assignment lowering
(`HirExprKind::Tuple` arm of `HirStmt::Assign` in
`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`) — extracted each
element with a bare `rt_tuple_get` and stored the tagged RuntimeValue verbatim.

Repro (routed shape, verified on the refreshed baseline seed
`bin/simple.exe` build-commit 0791c2b7f4a7):

```
fn main():
    val t = (10, 20)
    var c: i64 = 0
    var d: i64 = 0
    (c, d) = t
    print c          # JIT: 80   interpreter: 10
    print d          # JIT: 160  interpreter: 20
```

Everything the 2026-08-17 record listed as correct stayed correct (val
-destructure, array-destructure, whole-tuple assign, `t.0` reads); only the
destructuring-assignment lowering missed the unbox — exactly the omission this
record predicted could exist at "the destructuring-assign lowering site".

Two defects at the same site, both fixed in one change:

1. **Raw tagged word into typed sinks** — fixed by decoding each extracted
   leaf through the shared type-directed unbox tail
   (`unbox_dict_read_result`, the same tail the fixed `.get()` path reaches
   via `lower_index_expr`): int unbox (+ `UnitNarrow` for narrow widths),
   float unbox, u64 wide-word unbox, string cast, aggregate/ANY passthrough.
2. **Global sinks silently dropped** — the generic leaf path ran
   `lower_lvalue(Global)`, which is a dynamic value lookup, NOT an address;
   the subsequent `Store` wrote nowhere the global read path observes (sink
   kept its initial value under JIT). Global leaves now mirror the plain
   `g = v` arm: `GlobalStore` with the `box_scalar_for_tagged_slot` tail.

Out of scope, observed while pinning (front-end rejects in BOTH engines, so
they cannot exercise this JIT site): labeled-tuple destructuring assignment
("tuple unpacking requires tuple or array"), nested-array patterns inside a
tuple unpacking ("tuple unpacking target must be identifier"). The nested
arm keeps its existing raw-handle behaviour, unchanged.

Pin (mirrors the int-width matrix pattern: run-path probe + subprocess spec,
absolute-literal oracles, dual-engine):

- `test/01_unit/compiler/codegen/probe_tuple_destructuring_assign_jit.spl`
- `test/01_unit/compiler/codegen/tuple_destructuring_assign_class_spec.spl`

Verified on the seedfix seed built from work/seedfix-20261111: probe 22/22 PASS
under BOTH `SIMPLE_EXECUTION_MODE=interpreter` and `=jit` (baseline seed: 15
FAIL / 7 PASS under JIT); spec verdict OK 2/2 via
`SIMPLE_LIB=src SIMPLE_BINARY=<seed> SIMPLE_BIN=<seed> <seed> test
test/01_unit/compiler/codegen/tuple_destructuring_assign_class_spec.spl
--mode=interpreter --no-cache`.
