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
