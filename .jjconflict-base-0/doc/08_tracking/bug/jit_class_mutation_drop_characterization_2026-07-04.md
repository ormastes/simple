# Class-in-array mutation drop in interpret mode — characterization (task #112)

- **Status:** SOURCE FIX LANDED (2026-07-04) for the 70.backend `InterpreterBackendImpl` (class reference model, see bottom section) — pending REGATE on a healthy stage4 binary. `compiler.core.interpreter` (flat-AST) was found already-correct for this repro; the observed `42` on the deployed binary is source/binary divergence.
- **Discovered:** 2026-07-04 (task #112, following up on #108's discriminator work and #35's
  `struct_param_mutation_semantics_2026-07-03.md`)
- **Area:** interpreter runtime — class/array reference semantics
- **Severity:** High — silently drops mutations to class instances read out of an array

## Repro

Minimal repro, no function-call boundary involved:

```spl
class Counter:
    var val: i64

fn main():
    var arr = [Counter(val: 42)]
    var c = arr[0]
    c.val = 777
    print(arr[0].val)

main()
```

| Mode | Result |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpret bin/simple run` | `42` (WRONG — mutation lost) |
| default `bin/simple run` (JIT/compiled) | `777` (correct) |

Also reproduces with the mutation performed inside a called function
(`fn bump(arr: [Counter]): var c = arr[0]; c.val = 777`), and via `bin/simple
test` running `test/03_system/interpreter/interp_value_semantics_b35_spec.spl`
(new "Task 112" cases added in this pass — see below): both fail against the
currently-deployed binary.

A companion case in the same repro family — appending to a whole-array
**value-type** param inside a callee — also currently **leaks** to the caller
(`arr.push(999)` inside a free fn is visible to the caller's array afterward),
which is backwards: per `doc/08_tracking/bug/struct_param_mutation_semantics_2026-07-03.md`
and this spec file's own header comment, "ARRAYS are VALUE types: copied on
pass/assign." That is a second, independent defect surfaced by this pass —
tracked here since it was found by the same investigation, not previously
filed anywhere else.

## Source archaeology: `compiler.core.interpreter` (flat-AST) does NOT show this bug

Careful, direct reading of the current HEAD source of the flat-AST interpreter
(`src/compiler/10.frontend/core/interpreter/{eval_calls,eval_access,eval_stmts,value}.spl`)
finds no mechanism that would produce the observed `42`:

- `eval_index_expr` (`eval_access.spl:87`) returns `elements[idx]` directly —
  no copy of the element's value_id.
- `var c = arr[0]` (a local `var` declaration) goes through no copy path at
  all; `env_define` just binds the name to the same value_id. There is no
  struct/array copy logic anywhere outside `eval_calls.spl`'s function
  param-bind loop (confirmed via `grep -n val_struct_deep_copy`), and even that
  loop only fires for `val_is_struct(pval) and interp_struct_is_value_type(pval)`
  — arrays are never struct-kind, so an array param is never copied, and this
  repro doesn't even cross a function boundary.
- Field assignment (`eval_assign_expr`, `eval_access.spl:285`) calls
  `val_struct_set_field_idx(base_val, idx, new_val)`, which mutates
  `val_struct_values[vid]` — a single **global**, vid-indexed table
  (`value.spl:287`) — in place. Since `c` and `arr[0]` share the same `vid`
  (no copy ever created a second one), this mutation must be visible through
  both aliases.

By this reading, the current flat-AST source already implements correct
class-reference / array-value semantics for this exact repro, with or
without #108's struct `is_value_type` discriminator (which doesn't even
apply here — no function call, no struct-kind copy triggered).

## Binary/source divergence (why this can't be trusted without a rebuild)

The deployed binary (`bin/release/x86_64-unknown-linux-gnu/simple`,
mtime **2026-07-03 12:40**) predates the two #108 commits
(`24967a6b4f77`, `09926cff2502`, both committed **2026-07-04 04:03:41**) that
added the `is_value_type` discriminator to this exact package. Confirmed
independently: `test/03_system/interpreter/interp_value_semantics_b35_spec.spl`
still fails its **pre-existing** "struct: mut-param direct field mutation
does NOT leak to caller" case against the live binary (`expected 999 to equal
1`) — a case the spec's own docstring claims was "fixed in task #91" and whose
fix is plainly present in the current `eval_calls.spl` source. That
pre-existing, unrelated failure is direct, independent proof the running
binary does not reflect current HEAD source for this package.

Given that, the `42` result for the class-in-array repro cannot be
attributed with confidence to a still-open bug in `compiler.core.interpreter`
— the divergence could equally be masking an already-correct fix. This task
attempted to resolve the ambiguity by rebuilding:

```
bin/simple build bootstrap
=== Stage 1: Compile with seed compiler ===
  Running: .../simple native-build --source src/app --entry-closure --strip
    --threads 1 --timeout 180 --entry src/app/cli/bootstrap_main.spl
    -o bootstrap/stage1/simple --backend=llvm-lib
  Compile failed (exit None)
Stage 1 FAILED
```

Stage 1 did not complete inside its 180s timeout (or crashed silently — exit
code not captured). This is a bootstrap-health issue, independent of #112,
and is out of scope to chase down in this pass (see the many open `stage4-*`
bug docs already tracked for this class of instability). Without a clean
rebuild, the deployed binary's behavior cannot be used as ground truth for
whether current source fixes or still has this bug.

## What was NOT changed here, and why

No edits were made to `compiler.core.interpreter`'s array/struct/class
handling in this pass: the current source, read line-by-line, already
implements the correct reference-vs-value semantics for the exact repro in
this bug. Making a further "fix" on top of code that already looks correct,
without being able to compile and run it, would be exactly the
unverifiable/"fake green" outcome this task was explicitly told to avoid.

The 70.backend HIR-based `InterpreterBackendImpl`
(`src/compiler/70.backend/backend/interpreter*.spl`) was also inspected as an
alternative candidate (its own docstring says it's for "optimized mode
only" and defers to `compiler.core.interpreter` for plain "interpret" mode,
but `GlobalFlags.interpreter_mode` defaults to `"optimized"` even under
`SIMPLE_EXECUTION_MODE=interpret`, so it cannot be ruled out as the active
engine). It represents runtime class instances via the same `Value.Struct
(type_, fields: Dict<text, Value>)` variant used for plain structs — the
`Value.Object(ObjectValue)` variant that would give classes distinct
(reference) representation is declared in `backend_types.spl` but is **dead
code**: `grep -rn "ObjectValue|Value.Object"` across
`src/compiler/70.backend/backend/*.spl` (excluding the declaration file)
returns nothing. If this backend is in fact what executes `interpret` mode,
giving it a real struct-vs-class discriminator (mirroring #108's
`is_value_type` approach, or boxing class instances behind a handle into a
shared mutable table like the flat-AST engine's `val_struct_values[vid]`)
is the architecture-level fix — but confirming this backend is the active
one, and validating the fix, both require the same blocked rebuild.

## Recommendation / follow-up

1. **Unblock the bootstrap** (Stage 1 `native-build` timing out/crashing on
   `src/app/cli/bootstrap_main.spl` with `--backend=llvm-lib`) — needed before
   any interpreter-semantics fix in this area can be verified end-to-end.
2. Once a clean rebuild is available, re-run
   `test/03_system/interpreter/interp_value_semantics_b35_spec.spl` (extended
   in this pass with two new "Task 112" cases, see below) and the standalone
   repros above under both `SIMPLE_EXECUTION_MODE=interpret` and default mode.
   If the flat-AST source's already-correct-looking logic holds, all new
   cases should pass without further code changes; if not, that will finally
   be real (non-stale) evidence of a genuine remaining source bug.
3. If the 70.backend `InterpreterBackendImpl` turns out to be the active
   engine, give it the same struct-vs-class discriminator #108 added to the
   flat-AST engine (or box class instances via a handle rather than inlining
   `Dict<text, Value>` directly in the enum payload), and delete the dead
   `Value.Object`/`ObjectValue` machinery once its replacement lands (or wire
   it up instead, if that's the intended long-term representation).
4. Second defect found in passing (array param leaking an in-callee
   `push`/append back to the caller) needs the same rebuild-then-verify
   treatment; tracked here rather than a separate doc since it surfaced from
   the same investigation and repro family.

## Spec coverage added in this pass

`test/03_system/interpreter/interp_value_semantics_b35_spec.spl` — two new
`describe` blocks:

- "Task 112 - class-in-array reference semantics": `array_class_mutate_b35`
  reads a class element out of an array param into a local var and mutates it
  through a method call; expects the mutation visible via the original array
  slot. **Currently FAILS** against the deployed (stale) binary
  (`expected 42 to equal 777`).
- "Task 112 - array value semantics on parameter passing": `array_append_b35`
  appends to an array param inside a callee; expects the caller's array
  length unchanged. **Currently FAILS** against the deployed (stale) binary
  (`expected 4 to equal 3` — the append leaked).

Both are left in the spec file as honest, currently-failing regression
markers (matching the file's existing precedent of the still-failing
"mut-param direct field mutation" case) — not skipped, not marked passing.
They should be revisited once the bootstrap blocker above is resolved and a
fresh binary is deployed.

## Source fix landed (2026-07-04, task #112 code portion) — 70.backend class reference model

The 70.backend `InterpreterBackendImpl` (recommendation #3 above) was given a
real struct-vs-class discriminator via the object-handle model the prior team
settled on. Classes now have REFERENCE semantics; structs keep VALUE semantics.

### What changed (pure `.spl`, MAIN)
- **`src/compiler/70.backend/backend/objects.spl`** (new): `ObjectStore` — a
  shared registry (`records: [ObjectRecord]`, handle = index) with `me alloc`
  / `get_field` / `me set_field`. Reference-typed (mirrors `Environment`'s
  `me`-method style) so all `EvalContext` copies that share one `Environment`
  share one store.
- **`src/compiler/70.backend/backend_types.spl`**: `ObjectValue` redefined
  `{class_name: text, handle: i64}` (was the dead `{class_: SymbolId, fields:
  Dict}`). `Value.Object` now carries only a handle → copying a `Value.Object`
  copies the int handle → all copies alias one store record (reference sem for
  free; the exact #112 array-share symptom is fixed by construction).
- **`src/compiler/70.backend/backend/env.spl`**: `Environment` gains
  `store: ObjectStore` (init in `new()`).
- **`src/compiler/70.backend/backend/interpreter.spl`**:
  - `try_construct_struct` allocates a store record for CLASSES (returns
    `Value.Object(handle)`); STRUCTS still return `Value.Struct`.
  - Field access: a `Value.Object` arm dereferences the store. It is placed
    BEFORE the always-true struct-shadowed `Value.Struct` arm (`Object` is not
    struct-shadowed, so its test is genuinely refutable and only real Objects
    take it; Structs fall through).
  - Field assignment (`c.x = v` / `c.x op= v`): disc-dispatched `Field` target
    (`hash("Field")=21232742`) mutates the shared store — previously field
    assignment was `not_implemented` entirely.
- **`test/01_unit/compiler/interp_object_store_ref_model_spec.spl`** (new):
  source-driven spec (imports resolve from source, #31/#45) — class-share,
  struct-isolation, and class-in-array-share asserts driving the store directly.

### Verification honesty (this session could NOT observe the engine run)
The stage4 binary is corrupted by the concurrent #122/#123 seed work, so `bin/
simple lint`/`test` cannot execute (`rt_cli_run_lint is not supported in
interpreter mode`) and the interpreter engine cannot be observed. Substituted
gate: a seed fast-path `native-build` (isolated `--cache-dir`, `--target
x86_64-unknown-linux-gnu`) of a probe entry that transitively imports the four
changed modules + drives the full `ObjectStore`/`Value.Object` API →
**633 compiled, 0 cached, 0 failed**; the compiled-module set explicitly
includes `backend__backend__objects`, `backend__backend__backend_types`,
`backend__backend__env`, `backend__backend__interpreter`. Proves parse + lower +
typecheck + codegen + link are clean; does NOT prove runtime behavior.

### Post-gate REGATE checklist (run once a healthy stage4 binary is redeployed)
The coordinator rebuilds from main post-gate; once `bin/simple` runs cleanly:
1. `bin/simple lint` rc=0 on the four changed files + the new spec (the check
   that could not run this session).
2. `bin/simple test test/01_unit/compiler/interp_object_store_ref_model_spec.spl`
   — all three asserts (class-share / struct-isolation / class-in-array share)
   pass under the real self-hosted binary.
3. The standalone #112 repro at the top of this doc under
   `SIMPLE_EXECUTION_MODE=interpret bin/simple run` prints **777** (was 42).
   NOTE: confirm FIRST whether `interpret` mode actually routes to the
   70.backend `InterpreterBackendImpl` (this fix) vs the flat-AST
   `compiler.core.interpreter` — `GlobalFlags.interpreter_mode` defaults to
   `"optimized"`. If it routes to the flat-AST engine instead, the repro is
   governed by #108's `is_value_type` path, not this change; verify both.
4. Regression: `struct`-typed values still copy by value (no aliasing) — the
   `interp_value_semantics_b35_spec.spl` struct cases must stay green.
5. Confirm nothing else consumed the OLD `ObjectValue{class_, fields}` shape
   (grep was clean this session: only re-exports in `backend.spl`/`__init__.spl`).
6. Companion defect (array-param `push` leaking to caller, item #4 above) is
   NOT addressed by this change and remains open.
