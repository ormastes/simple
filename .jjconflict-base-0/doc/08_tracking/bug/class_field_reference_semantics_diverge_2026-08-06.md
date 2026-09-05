# Class reference semantics diverge: interpreter value-copies class fields; JIT crashes on optional class field

- **Filed:** 2026-08-06
- Status: OPEN (P1) — **defect 1 re-reproduced by EXECUTION 2026-09-02, and the
  repro fixture no longer runs to completion. See "Re-reproduction 2026-09-02".**
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  localized to the out-of-scope Rust seed; every reachable pure-Simple candidate interpreter was
  checked and does not share this defect, but none is buildable/runnable in this tree today, so no
  bounded, verifiable fix location exists yet.
- **Severity:** High — silently breaks every zero-copy aliasing design (packed-scene writers, arenas)
- **Component:** seed tree-walk interpreter (value-copy) + seed JIT (Option-field nil crash)
- **Found by:** LANE F1 of the render-perf redesign plan (§4.1)

## Contract under test

`class` = identity/reference semantics: assigning a class to a field, array
slot or parameter copies the REFERENCE. `struct` = value semantics. All
engines must agree. Today they do not — this is exactly what forced
`UiSceneNativeWriter` to own growable temporary arrays and row-copy into the
arena instead of writing through a field reference.

## Measured truth table

Fixture: `test/fixtures/repro/compiler/class_identity/class_field_reference_semantics_repro.spl`

Binary: Rust bootstrap seed `bin/release/x86_64-unknown-linux-gnu/simple`
(md5 `ed53cc5f255e269ca27c4cd83b17aef9`) — what `bin/simple` currently is.

| case | JIT (default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| 1 mutate original, read via field | REF ✅ | **COPY** ❌ |
| 1b mutate via field, read original | REF ✅ | **COPY** ❌ |
| 2 nested (`Outer.inner.cell`) | REF ✅ | **COPY** ❌ |
| 3 class ref in array element | REF ✅ | **COPY** ❌ |
| 4 class as fn parameter | REF ✅ | REF ✅ |
| 6 field re-assignment after construction | REF ✅ | **COPY** ❌ |
| 5 optional class field (`Cell?`) | **CRASH** — `runtime error: field access on nil receiver` + core dump | **COPY** ❌ |

Two distinct defects:

1. **Interpreter value-copies class references everywhere except plain fn
   parameters.** Every field store (construction or re-assignment) and array
   store snapshots the object. Only argument passing aliases.
2. **JIT: an optional class field (`maybe: Cell?`) reads back as nil** —
   `oh.maybe` is nil immediately after `OptHolder(maybe: c5)`, so any access
   dies with "field access on nil receiver" and dumps core. This crashes even
   when the read is hoisted to a local first. Separate defect; filed here
   because the same fixture exposes it.

## Re-reproduction 2026-09-02 (aarch64-apple-darwin) — plus a NEW blocker

Binary: `bin/release/aarch64-apple-darwin/simple`, 29,315,096 bytes, mtime
2026-07-25 14:15:52, sha256 prefix `f2c216a660da83da1a253d2e8191a305`,
`--version` -> `Simple v1.0.0-beta`; prints the Rust-seed banner on `run`, so
this attributes to the **seed** engine. (`bin/simple` is the bootstrap CLI and
has no `run` at all — probing it proves nothing about this defect.)

Running the fixture this record names:

```
$ <binary> run test/fixtures/repro/compiler/class_identity/class_field_reference_semantics_repro.spl
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
  Memory safety error [W1006]: mutation without mut capability (field_0):
  mutation requires `mut` capability on the receiver while lowering bump at 31:9
1 field<-original      = COPY(n=10)
1b original<-field     = COPY(n=20)
error: semantic: invalid assignment: deeply nested field access requires intermediate variables
```

Two things, one confirming and one new:

1. **Defect 1 still reproduces.** Cases 1 and 1b both report `COPY`, i.e. the
   interpreter still value-copies a class reference stored into a field, exactly
   as the truth table says. Localization is unchanged and still points at
   `src/compiler_rust/**` (`class_instantiation.rs` building instances as
   `fields: Arc::new(fields.clone())`), which is out of scope by policy — that
   is the reason this stays open, not a missing reproduction.

2. **NEW — the fixture no longer runs to completion, so the truth table above
   cannot currently be regenerated.** It aborts at case 2 (nested
   `Outer.inner.cell`) with `semantic: invalid assignment: deeply nested field
   access requires intermediate variables`. Cases 2, 3, 4, 6 and 5 are therefore
   unmeasured as of this date — the rows for them in the table are historical.
   Note the JIT lane is also not being exercised: the W1006 memory-safety error
   above forces a fallback to the interpreter before any JIT measurement happens,
   so "the JIT crashes on an optional class field" (defect 2) was likewise not
   re-observed. Whoever resumes this must first repair the fixture (split the
   nested access into intermediate variables, and give case 1's receiver the
   `mut` capability W1006 demands) before any engine comparison is meaningful.

## Repro commands

```
bin/simple run test/fixtures/repro/compiler/class_identity/class_field_reference_semantics_repro.spl
SIMPLE_EXECUTION_MODE=interpret bin/simple run <same>
```

(Case 6 is ordered before case 5 in the fixture because the JIT crash on 5
would otherwise truncate the table.)

## Localization

- **Interpreter (measured):** Rust seed tree-walk interpreter.
  `src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs`
  builds instances as `fields: Arc::new(fields.clone())` — construction
  snapshots field values into a fresh map, so a class value stored into a
  constructor argument (and, per case 6, a later field store) is copied, not
  aliased. `src/compiler_rust/**` is **out of scope by policy**; no fix
  attempted there.
- **Pure-Simple interpreter** (`src/compiler/interp/mir_interpreter.spl`,
  SetField path) could not be measured: no pure-Simple binary is built in this
  tree. Do not assume it matches either engine; measure before claiming.

## Consequence

The plan's F1 gate ("same corpus, same hashes on every engine") is the
prerequisite for the packed span ABI (F2) and the direct arena writer (F3).
Until the interpreter honors reference semantics, any writer holding a class
field reference to an arena is engine-dependent, and interpreter-mode tests of
zero-copy code are testing a different program.

## Related

- `test/01_unit/compiler/class_reference_semantics_spec.spl` — contract spec.
- Memory: tuple-of-class return does not preserve mutation visibility
  (interpreter) — same family.
- Interpreter Option encoding uses `__tag`; seed `.?` lowers to bool.

## Investigation update (2026-08-06, second pass)

Re-confirmed the truth table exactly as measured above by re-running both repro
commands against the current `bin/simple` (still the Rust seed, same md5
`ed53cc5f255e269ca27c4cd83b17aef9`) — cases 1/1b/2/3/6 = COPY under
`SIMPLE_EXECUTION_MODE=interpret`, case 5 core-dumps the JIT, matching the doc
verbatim.

Went looking for a pure-Simple interpreter this fix could actually land in
(per repo policy: `src/compiler_rust/**` is out of scope; "fix .spl not Rust").
Found and reviewed **every** pure-Simple interpreter tier that exists in this
tree, with these results:

1. **`src/compiler/10.frontend/core/interpreter/` ("core interpreter", has the
   `_EvalOps/` subfolder the task pointed at).** Read `eval_calls.spl`,
   `_EvalOps/access_literal_assign_eval.spl`, `value.spl`. This tier represents
   every struct/class instance as an index (`value_id`) into a global arena of
   parallel arrays (`val_struct_values: [[i64]]`, etc.) — field storage,
   `eval_struct_lit` (construction), `eval_assign_expr`'s `EXPR_FIELD_ACCESS`
   branch (re-assignment), and array-literal/array-store all read and write
   this arena **by value_id, never copying**. The only copy in the entire
   package is `val_struct_deep_copy`, called from the function-call
   parameter-binding loop in `eval_calls.spl` (~line 342), and it is
   *conditioned on* `interp_struct_is_value_type(pval)` — a decl-level flag
   (`decl_set_is_value_type`, task **#108**, already landed) that is `false`
   for class-origin decls. So class instances are structurally *never* copied
   anywhere in this tier — cases 1/1b/2/3/6 could not reproduce here even in
   principle, because the representation has no copy-on-store code path for a
   class to fall into. This is not a fix I made; it is how the existing code
   is already shaped.
   - **Could not be dynamically verified.** `core_interpret`/`core_interpret_expr`
     (the actual entry points, in `mod.spl`) transitively depend on
     `jit_init_with_backend`, which only exists inside a compiled self-hosted
     binary — none exists in this tree. Confirmed by running a minimal harness
     through `bin/simple run`: `error[E1002]: function 'jit_init_with_backend'
     not found`. This matches `test/02_integration/compiler/core_interpreter_intensive_spec.spl`'s
     own `_can_run = false` gate and its comment: "these tests require compiled
     mode; the core interpreter functions ... are not available in interpreter
     mode." This whole tier is presently dead code from the point of view of
     anything `bin/simple test`/`bin/simple run` can execute today.
   - A follow-up attempt to validate the underlying arena primitives directly
     (bypassing `core_interpret`, calling `val_make_struct`/`val_struct_set_field_idx`
     from a standalone harness) surfaced an *unrelated* reliability problem in
     the Rust seed's own interpreter: a function that returns an array read
     from a mutated global `var` can return stale data even though a direct
     index read of the same global sees the fresh value (repro not kept in the
     tree; not one of the two bugs this doc/its sibling track, and it lives in
     the same out-of-scope Rust seed — flagging only so it isn't mistaken for
     evidence about the pure-Simple tier above, whose only faithful executor
     turned out to be the very engine under test).
2. **`src/compiler/95.interp/mir_interpreter.spl`** (the file this doc's
   "Localization" section above names as unmeasured). `Aggregate`/`GetField`/
   `SetField` model memory as a flat `locals: {i64: i64}` map keyed by
   `base_address + field*8`; an aggregate's "value" is just its base address
   (an `i64`). Copying that address anywhere is a pointer copy by
   construction — there is no per-field snapshot step for this tier either.
   Same caveat: this operates on lowered MIR, not source, and has no
   standalone harness path checked in this session.
3. **`src/compiler/70.backend/backend/objects.spl`** — a handle-based
   `ObjectStore` + `Value.Object(handle)` model built for exactly this
   contract (task **#112**), already covered by its own passing spec,
   `test/01_unit/compiler/interp_object_store_ref_model_spec.spl`, which
   drives it from source independent of any binary and asserts the same
   REF-not-COPY behavior this doc wants (see its "class-share" /
   "class-in-array share" examples).

**Conclusion:** the defect is real, fully reproduced, and its root cause is
exactly where already localized — `class_instantiation.rs`'s
`fields: Arc::new(fields.clone())` snapshot on construction, in
`src/compiler_rust/compiler/src/interpreter_call/core/` — which remains
out of scope by policy. No other in-scope, buildable code path in this tree
currently reproduces the bug, so there is nothing bounded to change in
pure-Simple source without first landing a self-hosted binary (a separate,
much larger undertaking, and explicitly not attempted here per "no bootstrap
unless essential"). Leaving Status as blocked/investigated rather than
claiming a fix.
