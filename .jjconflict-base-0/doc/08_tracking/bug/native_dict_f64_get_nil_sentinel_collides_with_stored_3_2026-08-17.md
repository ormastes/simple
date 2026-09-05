# Native/JIT `Dict<_, f64>.get()` conflates nil with a stored `3.0`

- **Status:** RESOLVED 2026-08-18 — fixed in the seed MIR lowering + Cranelift codegen; `check-dict-engine-differential.shs` PASSes 13/13
- **Detected by:** `sh scripts/check/check-dict-engine-differential.shs` — case `text_f64_local`
- **Severity:** silent wrong answer, both directions, no diagnostic
- **Related:** `doc/07_guide/language/dict_native_pitfalls.md` truth table, row
  "`d.get(k)` — miss, `V` = `f64`", which until now read
  **"unverified on the JIT/self-hosted lane"**. It is no longer unverified: it
  reproduces, and it is *worse* than the row described.

## Summary

On a `Dict<K, f64>`, `.get()`'s nil discrimination is broken in **two opposite
directions** at once:

1. **A genuine miss is reported as present**, decoding to `0.0`. `?? default`
   does not fire and `== nil` is `false`.
2. **A stored `3.0` is reported as nil.** `?? default` fires and `== nil` is
   `true`, for a key that is present with a perfectly ordinary value.

Only `V = f64` is affected, and only `.get()` — the `d[k]` bracket read returns
`3.0` correctly, which proves the value is *stored* fine and localises the defect
to `.get()`'s nil-guard path.

## Measurement

Binary identity (recorded per `.claude/rules/commands.md` — the symlink target is
replaced by other lanes mid-session):

```
binary:   /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
identity: 59537240 2026-08-17 12:58:51.339525019 +0000   (the Rust seed)
loadavg:  15.31 17.39 21.29
```

Engine witness: the JIT arm printed `[jit-addr] probe 0x...`
(`SIMPLE_JIT_TRACE_ADDR=1`) and ran with `SIMPLE_JIT_STRICT=1`, so it is
confirmed JIT-compiled and not a silent interpreter fallback. The interpreter arm
is the oracle (`SIMPLE_EXECUTION_MODE=interpret`).

Probe: a `Dict<text, f64>` holding `v3=3.0`, `v4=4.0`, `v0=0.0`, `vn=-1.0`.
Verbatim diff, oracle vs JIT:

```
 len=4
-get_v3=3.0
+get_v3=-99.0
 get_v4=4.0
 get_v0=0.0
 get_vn=-1.0
-get_miss=-99.0
-get_miss_isnil=true
-get_v3_isnil=false
+get_miss=0.0
+get_miss_isnil=false
+get_v3_isnil=true
 bracket_v3=3.0
```

`v4`, `v0` and `vn` are all correct, so this is not general f64 corruption — it is
specific to the value `3.0` and to the miss case.

## Mechanism — the value `3.0` is not a coincidence

This is precisely the landmine `dict_native_pitfalls.md` predicted without
measuring. The flat-`Option` ABI uses the integer `3` (`RT_NIL`) as its nil
sentinel. The nil lane of the dict-get guard materialises that sentinel with a
**numeric cast** into the merge type, and casting the *integer* `3` to `f64`
yields the real float `3.0` rather than the bit pattern `3`. So:

- a **stored** `3.0` compares equal to the materialised sentinel and is
  misclassified as nil (direction 2);
- and because `guardable_value_type` excludes f64, the miss sentinel is fed
  through the ordinary f64 decode arm and emerges as `0.0` rather than nil
  (direction 1).

A fix needs a **bitcast** (or an i64-typed merge with the bitcast on the value
lane), *not* merely adding `f64` to `guardable_value_type` — a one-line predicate
addition would make the guard compare a real `3.0` against a real `3.0` and would
keep misfiring on a stored `3.0`.

## Scope of this measurement — stated plainly

`bin/simple` is currently the **Rust seed** (it says so at every invocation), so
the two arms above are the seed's tree-walk interpreter and the seed's Cranelift
JIT. The pure-Simple `guardable_value_type` /
`dict_get_preserve_flat_nil` in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
is **not** executed by this run. What is measured is therefore: *the seed's
native lane has this defect*. Whether the self-hosted MIR lowering has it too is
**not established here** — though the mechanism above is representation-level and
the pitfalls doc predicts the same collision there. The guard will answer that
question automatically once `bin/simple` is a self-hosted binary, with no edit.

## Rows that were re-verified GREEN in the same run

The other 12 cases AGREE between the two engines, which converts several
previously-luck-based fixes into standing regression coverage:

- `.len()` on local, class-field and chained class-field dicts (the old `-1`
  defect does not reproduce)
- `.get()` hit and miss for `i64`, `text`, `bool`
- `.get()` hit and `d[k]` for struct-, class- and enum-valued dicts
- array-valued dicts, both local and **class-field** bracket reads (the truth
  table's "class-field `d[k]` on array values segfaults" row did **not**
  reproduce on either arm)
- `contains_key` on a struct-valued `Dict<i64, Scope>` — the operation whose
  under-reporting SIGSEGVed Stage 3 (see the long comments at
  `src/compiler/20.hir/hir_types.spl` `lookup()` / `lookup_or_invalid()`).
  All 6 inserted keys reported present on both arms.
- the reported **bootstrap-blocker shape** — a class-field `Dict<i64, Sym>`
  reached through two chained field hops (`o.inner.syms[k]`), read repeatedly —
  was **stable and a correct bijection** on both arms in this seed. That defect
  is being fixed on another lane; this case is its acceptance test and does not
  reproduce on the seed's engines, consistent with it living in the self-hosted
  MIR lowering.

## Reproduce

```sh
sh scripts/check/check-dict-engine-differential.shs
sh scripts/check/check-dict-engine-differential.shs --only=text_f64_local
```

Verdict line, verbatim:

```
FAIL — 13 case(s) checked, 1 diverged from the interpreter oracle: text_f64_local
```

## Re-verified STILL OPEN + seed-side site located (2026-08-17)

Binary identity unchanged from the measurement above (`59537240 2026-08-17
12:58:51`). Guard re-run, verdict verbatim (last line of stdout):

```
$ sh scripts/check/check-dict-engine-differential.shs --only=text_f64_local
FAIL — 1 case(s) checked, 1 diverged from the interpreter oracle: text_f64_local
```

The diff is byte-identical to the one recorded above (`get_v3=-99.0`,
`get_miss=0.0`, `get_miss_isnil=false`, `get_v3_isnil=true`).

**Seed-side localisation.** In the Rust seed the f64 arm has no nil
discrimination at all — it is not that the sentinel is cast wrongly, it is that
nothing looks for it:

- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs:290` routes
  `d.get(k)` through `lower_index_expr`, whose unbox tail is
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:760-769`
  (`unbox_dict_read_result`): for `TypeId::F32 | TypeId::F64` it emits an
  unconditional `MirInst::UnboxFloat` and returns. There is no branch on the
  `RuntimeValue::NIL` word (tagged `3`) anywhere on this path, whereas the int
  arm at least reaches a tag-aware `UnboxInt`.

That accounts for direction 1 (a miss — the NIL word `3` — is fed to
`UnboxFloat` and emerges as `0.0`, so `?? default` never fires). Direction 2 is
the downstream half: the surviving nil test compares against the integer
sentinel `3` (`codegen/instr/pattern.rs:45-50` and `codegen/instr/basic_ops.rs:
316-320` both materialise `iconst 3`), and against an already-unboxed `f64` a
stored `3.0` matches it.

Both halves are RUST SEED code; not fixed here per this task's rules. The
mechanism paragraph above stands, with one correction: on the seed lane there is
no cast of the sentinel *into* f64 on the get path — the get path simply never
tests for nil, and the collision happens at the later comparison.

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (the pure-Simple
`guardable_value_type` / `dict_get_preserve_flat_nil`) was NOT executed by this
run and is not implicated by it — unchanged from the scope note above.

## RESOLVED 2026-08-18

### Root cause (confirmed, both directions, one representation gap)

After `d.get(k)` on a `Dict<_, f64>` is unboxed there is **no f64 bit pattern
that means "absent"**, and the surviving nil test compares against the *numeric*
sentinel:

1. `MirInst::UnboxFloat` lowers to `rt_value_as_float(v)`, which maps the NIL
   word `3` to a perfectly ordinary `0.0`. A genuine miss therefore decodes to
   `0.0` and `?? default` never fires.
2. `HirExprKind::Nil` lowers to `ConstInt 3`
   (`mir/lower/lowering_expr_literal.rs::lower_nil_expr`), and
   `coerce_binop_operands` (`codegen/instr/core.rs`) coerces a mixed int/float
   pair to float — so `x == nil` on an f64 became `fcmp x, 3.0`, and a
   legitimately **stored** `3.0` reported itself as nil.

`d[k]` was correct only because the guard's bracket case is a hit with no nil
test on it — the same MIR path is used for both reads.

### Fix (smallest correct encoding change, no Option redesign)

The float representation of "absent" is now the f64 whose **bits** are the nil
word, `f64::from_bits(3)` (the denormal `1.5e-323`), rather than `0.0`:

- `src/compiler_rust/compiler/src/codegen/instr/mod.rs`, `MirInst::UnboxFloat`:
  after `rt_value_as_float`, a `select` on `raw == 3` yields `f64::from_bits(3)`.
  Only the exact word `3` selects the sentinel; every non-nil input is untouched.
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`,
  `lower_binary_expr`: an `Eq`/`NotEq` whose one side is `HirExprKind::Nil` and
  whose other side is `F32`/`F64` now compares against `ConstFloat(f64::from_bits(3))`
  instead of the integer `3`, so `3.0` and "absent" are distinct constants.

Both halves are **Rust seed** code, as localised above. The Rust runtime
(`runtime/src/value/`) and the C runtime (`src/runtime/`) were evaluated
separately and **neither was changed** — `rt_value_as_float` keeps its existing
total behaviour for every other caller; the nil discrimination is added in the
compiler, where the static type that makes it decidable is available.

### Evidence — both arms, verbatim last stdout line

Reverted arm (unmodified sources, the shared session binary
`bin/release/x86_64-unknown-linux-gnu/simple`, `59621024`):

```
FAIL — 13 case(s) checked, 1 diverged from the interpreter oracle: text_f64_local
```

Fixed arm (private build of the same tree plus the two hunks above,
`/mnt/data/tmp/dictf64-target/release/simple`, `59581064 2026-08-18 00:26:22`):

```
PASS — 13 case(s) checked, every Dict operation agrees with the interpreter oracle
```

`text_f64_local` moved `AGREE`; the other 12 cases stayed `AGREE`. The guard's
own `--selftest` (comparator/witness/normalizer ablation) passed in the same run,
and the JIT arm carried its `[jit-addr] probe` engine witness under
`SIMPLE_JIT_STRICT=1`, so this is a real JIT result and not an interpreter
fallback.

No perf regression:

```
PASS — 2 check(s) checked, Dict lookup is sub-quadratic (6.10x for 4x input) and the hot lookup kept its O(1) shape
```

### Build scope — the shared binary was NOT touched

`cargo check --release --bin simple` returned RC=0 (read from a variable on the
next line, not through a pipe) and the demonstration binary was built into a
**private** `CARGO_TARGET_DIR=/mnt/data/tmp/dictf64-target`. `bin/simple`,
`bin/release/**` and the symlink were left exactly as other lanes found them; the
guard was pointed at the private build via `SIMPLE_BIN`. No bootstrap was run.

### Still open, deliberately

The pure-Simple self-hosted lowering
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`) is unchanged and was
not exercised by this run — the scope note above still applies. The guard will
answer that question with no edit once `bin/simple` is a self-hosted binary.
