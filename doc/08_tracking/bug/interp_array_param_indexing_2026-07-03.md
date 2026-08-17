# Interpreter: array parameters break indexing — [[text]] params misparse, [f64] param variable-index reads 0

**Date:** 2026-07-03
**Severity:** downgraded to low — see Re-triage 2026-08-01
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
and are contradicted by shipped code. 1 narrow symptom survives (2D index
assignment) and is a seed-interpreter lvalue gap, not an array-parameter bug.
The title of this doc is wrong: "array parameters" is not the variable.

## Symptoms

1. **`[[text]]` parameter misparse:** a function taking a `[[text]]` parameter
   fails to parse/compile indexing or iteration over it, while the same code
   with a `[[f64]]` parameter works.
2. **Variable index on array parameter reads 0:** indexing an array passed as
   a function parameter with a *variable* index returns 0 in the interpreter
   (literal indices work). Found during MMULT/MINVERSE implementation.
3. Related, previously known: 2D index assignment `a[r][c] = v` is
   unsupported; flat 1D assignment works.

## Workaround (in production use)

`src/app/office/sheets/formula.spl` matrix ops (MMULT, MINVERSE, MDETERM,
MUNIT) are written fully inline: matrices stored as LOCAL flat row-major
`[f64]` arrays indexed `row*cols+col`; no struct or array crosses a call
boundary. Only scalar helpers (`_mat_abs`, `_mat_snap`) are factored out.

## Also reconfirmed

`grid` as a local variable name produces a misleading
`expected Colon, found Dot` parse error (existing bug doc
`parser_grid_identifier_keyword_collision_2026-07-03.md`).

## Next step

Minimal repros for (1) and (2) in interpreter unit tests; likely the same
value-copy path as the Dict-in-struct corruption
([[interp_dict_in_struct_copy_corruption_2026-07-03]]) — parameter-passed
aggregates lose element addressing.

---

## Re-triage 2026-08-01 (static analysis only — ENOSPC, nothing executed)

Environment: btrfs metadata exhausted (1.00 MiB unallocated). No builds, no
`simple test`, no binary was run. Every claim below is source-level evidence at
HEAD; the two places where only execution could settle a question are marked
UNVERIFIED.

### Symptom 1 — `[[text]]` parameter misparse: NOT REPRODUCIBLE

`[[text]]` parameters parse, index, and iterate in shipped compiler code:

- `src/compiler/90.tools/stats/json_formatter.spl:210` `fn
  format_by_kind_json(by_kind: [[text]]) -> text:` with `val row = by_kind[i]`
  at `:214` — a **variable** index on a `[[text]]` parameter. Same shape at
  `:236` / `:240` (`format_by_module_json`).
- `src/compiler/90.tools/coupling/metrics.spl:55` `fn _cycle_seen(cycles:
  [[text]], cycle: [text]) -> bool:` iterates it with `for existing in cycles:`
  at `:56`.
- `src/compiler/70.backend/link_attrs.spl:71`,
  `src/compiler/10.frontend/core/types.spl:1126`,
  `src/compiler/90.tools/coupling/report.spl:337` — same.
- 144 files in `src/` + `test/` use `[[text]]`, including parameters
  (`test/01_unit/app/t32_cli/t32_cli_bridge_spec.spl` passes `rows: [[text]]`
  through `br_table` and asserts `r.rows[0][0] == "Key"` at `:231`).

The original report noted `[[f64]]` worked while `[[text]]` did not. There is no
element-type branch in type parsing that could produce that; the same doc's
"Also reconfirmed" section records a `grid` identifier/keyword collision
(`parser_grid_identifier_keyword_collision_2026-07-03.md`) in the same file being
written at the time, which is the more likely cause of the parse error attributed
here.

### Symptom 2 — variable index on an array parameter reads 0: NO MECHANISM

A parameter is not a distinguishable thing at index-read time in the seed
tree-walk interpreter. Argument binding evaluates each argument to a `Value` and
inserts it into the ordinary env map under the parameter's name:

- `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs:167`,
  `:197`, `:261`, `:306`, `:330`, `:474` — all `bound.insert(param.name.clone(),
  val)`.

After that insert, a parameter is byte-identical in the environment to a local
`val`, and index evaluation resolves the identifier out of the same map. There is
no param-vs-local branch for indexing to diverge on.

Independent falsifier in shipped code —
`src/compiler/90.tools/duplicate_check/math_utils.spl:33`:

```
fn cosine_similarity_dense(a: [f64], b: [f64]) -> f64:
    while i < a.len():
        dot_product = dot_product + a[i] * b[i]     # :46, variable index on [f64] param
```

`test/01_unit/app/duplicate_check/semantic_spec.spl:219-221` asserts
`cosine_similarity_dense([1,1,0]-ish identical vectors) > 0.99`, and `:230-235`
asserts `> 0.9` for similar vectors. If a variable index on an `[f64]` parameter
read 0, `dot_product` would be 0.0 and both expectations would fail. This spec
uses `use std.spec`, so it runs on the interpreter — exactly the engine the doc
accuses. UNVERIFIED: the spec could not be executed under ENOSPC, and this
suite's rows are absent from the current `doc/08_tracking/test/test_result.md`,
so this is a static falsifier, not a green run.

### Symptom 3 — `a[r][c] = v` unsupported: STILL TRUE (seed interpreter)

This one survives, and it is the only real defect in the doc.
`src/compiler_rust/compiler/src/interpreter/node_exec.rs:1027` handles an
`Expr::Index` assignment target. It enumerates exactly two receiver shapes:

- `:1033` `Expr::Identifier` — `arr[i] = v`
- `:1344` `Expr::FieldAccess` — `self.dict[k] = v`, `obj.arr[i] = v`

Anything else falls through to `:1435`:

```
"invalid assignment: index assignment requires identifier or field access as container"
```

For `a[r][c] = v` the outer target's receiver is itself an `Expr::Index`, so it
lands on that error. Note this is an **assignment-target coverage gap**, not
anything to do with parameters — it fails identically for a plain local.

A general place resolver that already handles this exists and is simply not
wired in: `src/compiler_rust/compiler/src/interpreter/place.rs:69`
`resolve_place` recurses through `Expr::Index` at `:99` and `Expr::FieldAccess`
at `:90`, with `write_place` at `:223`. It is called only from the
FieldAccess-*target* branch (`node_exec.rs:987`, `:1013`), whose own comment at
`:1010` claims "arbitrary projection chains are supported" — true for that
branch, false for the Index-target branch beside it.

### Is this specified value-semantics behaviour?

No — and the value-semantics rule does not apply to any of these symptoms.

`doc/06_spec/feature/language/data_structures_spec.md:37`, `:47`, `:97` and
`doc/06_spec/feature/language/memory_spec.md:37`, `:46`, `:84` specify value
semantics ("copied on assignment", "assignment copies the data") for **structs**.
Value semantics predicts *lost mutations* across a call boundary. Symptoms 1 and
2 are a **parse** failure and a **read** returning the wrong value — neither is a
mutation, so value semantics can neither excuse nor explain them; they simply do
not reproduce. Symptom 3 is a write, but it fails with a hard compile error
inside a single scope, not a silently-dropped mutation, so it is not the
value-semantics rule either.

### Family placement

Neither established family.

- **Family 1 (value encoding: `list.get(i)` shifted left by 3, `??` corrupting
  index 3, `[]`-born var rebound reading shifted)** is a *native/JIT* tagging
  family. The accusation here is against the tree-walk interpreter, which stores
  `Value` enums in a `HashMap` with no tag encoding to get wrong. Ruled out.
- **Family 2 (aggregates through function params lose mutations; return-the-
  object rule)** is about writes not propagating out. Symptoms 1-2 are parse and
  read. Ruled out.
- Symptom 3 is a third, much smaller thing: **interpreter lvalue/place coverage**
  — one `else` arm that predates the `place.rs` resolver and was never updated to
  use it.

### Engine scope

- Symptom 3 confirmed in the **seed tree-walk interpreter** only
  (`src/compiler_rust/...`), i.e. the engine `simple test` / `use std.spec`
  reaches.
- Seed JIT / native: UNVERIFIED, but `src/os/services/nvfs/core/arena.spl:456`
  ships `_bufs[idx][offset] = byte` in natively-compiled OS code, which implies
  native codegen accepts the form. If so this is seed-interpreter-only — matching
  today's pattern where several "interpreter" bugs proved seed-only.
- Pure-Simple lane: UNVERIFIED (no `IndexAssign` / nested-index handling found
  under `src/compiler/` by name; not established either way).

### Change I would make (NOT made)

One fallback, no new machinery: in `node_exec.rs` at the `:1435` `else` arm of
the `Expr::Index`-target branch, try
`super::place::resolve_place(&assign.target, ...)` + `place::write_place` before
returning the error — mirroring exactly what the FieldAccess-target branch
already does at `:1012-1018`. `place.rs` already recurses through `Expr::Index`,
so this covers `a[r][c] = v` and arbitrary deeper chains in a few lines. Guard it
with an interpreter unit test for `a[r][c] = v` and `a[r][c][d] = v`.

Not applied: ENOSPC forbids building or testing, and an interpreter lvalue change
must not land unbuilt.

### Recommended disposition

Rewrite this doc down to symptom 3 alone under a truthful title (interpreter
nested index assignment unsupported), or close it and file symptom 3 fresh.
Symptoms 1 and 2 should be struck. The `formula.spl` workaround (matrices kept as
local flat row-major `[f64]`, nothing crossing a call boundary) is no longer
justified by symptoms 1-2; the only part still justified is avoiding `a[r][c] =
v`, which flat row-major indexing sidesteps anyway. Removing the workaround is
safe to attempt but should be gated on an actual run, which ENOSPC blocked here.

---

## MECHANISM LOCALISED 2026-08-17 (measured, not inferred)

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
59536728 B, mtime 2026-08-16 22:59:37 (stale Rust seed, unchanged — no rebuild).
All probes inside `fn` bodies, both arms pinned via `SIMPLE_EXECUTION_MODE`,
`rc` read from a variable on the line AFTER the command. Every run below `rc=0`.
Engine-identity control `ctl()` returning `1152921504606846976` from inside a
`fn` printed `1152921504606846976` (interpreter) vs `-1152921504606846976`
(jit) in EVERY probe file, so the jit arm demonstrably compiled each time.

### It is a function-BOUNDARY effect, not array construction and not the annotation

One array value `[10, 20, 30]` built once in `main`, read four ways:

| probe | interpreter | jit | note |
|---|---|---|---|
| `arr.get(0)` read directly in `main` (defining frame) | 10 | **10** | correct |
| `fn f(a: Array<i64>) -> i64: return a.get(0)` | 10 | **80** | `10 << 3` |
| `fn f(a) -> i64: return a.get(0)` (no annotation) | 10 | **80** | annotation is irrelevant |
| `fn f(a: Array<i64>) -> i64: return a[0]` (bracket) | 10 | **80** | `.get` vs `[]` is irrelevant |
| build array in a fn, read via a local alias, never crossing a call | 10 | **10** | correct |

So neither the array literal nor the `.get`/`[]` spelling nor the type
annotation is the variable. The single discriminating factor is whether the
array is a function PARAMETER at the read site.

### It does NOT accumulate per boundary crossing

`hop1(a)` -> `hop2(a)` -> `a.get(0)` (two crossings) yields **80**, identical to
one crossing. So the array's stored contents are the same in both frames; the
divergence is entirely in how the READ SITE decodes, not in a per-call
re-boxing of the container. `a.len()` on the same parameter returns **3**
(correct) in both arms, and an `Array<String>` element read returns `"ab"`
(correct) — only int-typed element reads are affected.

### The arithmetic is done on DECODED values, and the RESULT is boxed once

This is the measurement that identifies the defective step. With `a = [10,20,30]`
passed as a parameter:

| expression | want | jit | decode |
|---|---|---|---|
| `a.get(0)` | 10 | 80 | `10 << 3` |
| `a.get(0) + 1` | 11 | **88** | `11 << 3`, NOT `80 + 1` |
| `a.get(0) * 2` | 20 | **160** | `20 << 3`, NOT `80 * 2` |
| `100 - a.get(0)` | 90 | **720** | `90 << 3`, NOT `100 - 80` |
| `a.get(0) == 10` | true | true | correct |
| `a.get(0)+a.get(1)+a.get(2)` | 60 | **480** | `60 << 3` |

`88 == 11 << 3` is decisive. If the tagged word were being fed into a native
`iadd` the answer would be `81`. It is not — the `rt_any_*` helpers decode both
operands correctly, compute the correct value, and RE-BOX the result as a tagged
ANY, exactly as `lowering_expr_ops.rs` documents. The arithmetic path is
correct. **The missing step is unboxing the ANY result at the typed sink.**

### Where the missing step is, in committed source

- `mir/lower/lowering_expr_struct.rs:614-694` (tail of `lower_index_expr`):
  emits `MirInst::UnboxInt` only when `element_expr_ty` is a concrete int type.
  When it is `TypeId::ANY` it falls to `else { Ok(raw_result) }` and returns the
  **still-tagged** word.
- `mir/lower/lowering_expr_method.rs:263-275` resolves the element type and
  `.unwrap_or(TypeId::ANY)` on failure. `receiver_is_array`
  (`lowering_expr_method.rs:42-48`) does NOT peel a `HirType::Pointer` layer,
  unlike the `FieldAccess`/`Index` arms of `recover_receiver_type`
  (`lowering_expr.rs:65-106`) which peel one explicitly with the comment
  "classes are frequently passed by pointer at the MIR boundary".
- `mir/lower/lowering_stmt.rs:885-889` ALREADY calls
  `unbox_scalar_for_raw_slot(ret_ty, v.ty, reg)`, whose comment describes this
  exact defect ("a RAW scalar return slot fed by a TAGGED value ... must be
  untagged, or the caller reads `v << 3`"). It does not fire here because its
  gate `slot_holds_tagged_value(value_ty)` (`lowering_core.rs:1441`) reads the
  **static HIR type** `v.ty`, which the typechecker has stamped as `i64` from
  the declared return type — while the value lowering actually produced is
  tagged. **The static type and the lowered representation disagree, and the
  unbox decision is made from the type that is wrong.**
- `lowering_expr_ops.rs:126-138` documents the same erasure and applies a
  band-aid for mixed ANY/concrete *operands*; nothing unboxes the ANY *result*
  at a typed sink. This is why `+ 1` still returns `11 << 3`.

**Correction to the earlier note above:** the comment in `lowering_expr_ops.rs`
asserts the element type is "genuinely unresolvable" for a list-typed parameter.
That premise does NOT hold for the probes here — `a: Array<i64>` is explicitly
annotated and still degrades to `ANY`. The element type is resolvable and is not
being resolved.

### Not part of this family (refuted by measurement 2026-08-17)

`rt_enum_discriminant` was proposed as a fourth member of this family on the
claim that it returns the constant `1337030607` for every receiver shape. That
claim is **refuted**. Probed with three provably DIFFERENT variants of one enum,
plus a non-enum, both arms pinned, rc=0:

| receiver | interpreter | jit |
|---|---|---|
| `Shape.Circle(1)` | 2403469957 | 2403469957 |
| `Shape.Square(1)` | 3299330368 | 3299330368 |
| `Shape.Blob` | 245049948 | 245049948 |
| `7` (not an enum) | -1 | `<value:0xffffffffffffffff>` |

Three different variants produce three DIFFERENT values, and a non-enum produces
`-1`. That is exactly the variant-name-hash contract documented in
`rt_enum_discriminant_is_enum_id_blind_name_hash_2026-08-08.md`. The
"same constant for every shape" report was an artifact of only ever observing
one variant. `rt_enum_discriminant` is NOT an untagging defect and does not
belong in this family.

Note the last row, though: the non-enum `-1` prints as `-1` under the
interpreter and as `<value:0xffffffffffffffff>` under jit. That is a raw `-1`
(all bits set, so `& 7 == 7`, an invalid tag) reaching a sink that expects a
TAGGED value — the INVERSE direction of this row's defect, and the same shape as
the `?? ` leak of `0xfffffffffffffcf7` (which is simply `-777` as a raw i64).
Those are a separate defect with an opposite fix and are not unified here.

Probe files (scratchpad, not committed): `p1.spl` .. `p7.spl`, `disc.spl`.

### ROOT CAUSE (exact line, 2026-08-17)

`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:379-394`,
inside `lower_index_expr`:

```rust
let element_expr_ty = if expr_ty == TypeId::ANY {
    self.type_registry
        .and_then(|tr| tr.get(receiver_ty))        // <-- RAW receiver_ty
        .and_then(|ty| match ty {
            HirType::Array { element, .. } => Some(*element),
            HirType::Dict  { value,   .. } => Some(*value),
            _ => None,
        })
        .unwrap_or(expr_ty)                        // <-- falls back to ANY
} else { expr_ty };
```

The element type is recovered from the **raw `receiver_ty`**. But this very same
function computed `recovered_receiver_ty` fifteen lines earlier
(`lowering_expr_struct.rs:349-353`) *precisely because* `receiver_ty` is
unreliable exactly here:

```rust
let recovered_receiver_ty = if receiver_ty == TypeId::ANY || receiver_ty.0 == u32::MAX {
    self.recover_receiver_type(receiver)
} else { Some(receiver_ty) };
```

`recover_receiver_type` is the function that resolves a `HirExprKind::Local`
that is a PARAMETER to `func.params[idx].ty` (`lowering_expr.rs:50-64`). The
adjacent `receiver_is_array` and the U64 test both correctly consult
`recovered_receiver_ty`; the element-type recovery does not. So for an array
PARAMETER the chain is:

1. `receiver_ty` is `ANY`/invalid -> `tr.get(receiver_ty)` yields `None`
2. `.unwrap_or(expr_ty)` leaves `element_expr_ty == TypeId::ANY`
3. `ANY` matches neither `needs_int_unbox` nor `needs_float_unbox`
   (`lowering_expr_struct.rs:615-627`), so the tail returns
   `Ok(raw_result)` -- the still-tagged word
4. the caller's `unbox_scalar_for_raw_slot` does not fire either, because its
   gate reads the static HIR type, which the typechecker stamped `i64`

...and the caller reads `v << 3`. For a LOCAL array `receiver_ty` resolves
directly at step 1, which is why the identical read in the defining frame is
correct. The correct array element type is available the whole time, in a
variable already in scope; it is simply not the one consulted.

### A prediction from that root cause that FAILED (recorded, not buried)

If the trigger were purely the read site failing to resolve the receiver's
type, then re-binding the parameter to a local with an explicit annotation
should resolve it. Measured (same binary, both arms pinned, rc=0, `ctl`
diverging so the jit arm compiled):

| probe | interpreter | jit |
|---|---|---|
| `return a.get(0)` (param direct) | 10 | 80 |
| `val b = a; return b.get(0)` | 10 | **80** |
| `val b: Array<i64> = a; return b.get(0)` | 10 | **80** |

The explicit annotation does NOT rescue it. This does not refute the
`lowering_expr_struct.rs:379-381` root cause -- the most likely reading is that
the annotation is not propagated into the local's `receiver.ty` either, so the
same `ANY` degradation occurs one hop later -- but it does mean the exact-line
root cause is a **source-supported hypothesis, not yet a measured fact**. The
value-side taint follows the parameter through a local rebinding, whereas a
local alias of a local ARRAY LITERAL (`val a = [10,20,30]; val b = a;
b.get(0)`) reads correctly as 10. Whatever is different about a parameter
survives an annotated copy.

**Settling it requires the build ablation** (fix reverted -> reproducer FAILS;
fix applied -> reproducer PASSES) against a privately-built seed. Until that is
run, treat the exact line above as the leading candidate and not as proven.
