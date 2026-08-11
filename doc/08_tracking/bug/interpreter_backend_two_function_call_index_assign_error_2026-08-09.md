# InterpreterBackendImpl.process_module fails on ANY module with a user-to-user function call

Status: FIXED 2026-08-09 (see "RESOLVED" section at the end)
Found: 2026-08-09, while verifying `test/01_unit/compiler/semantics/aspect_weave_spec.spl`
(C3 static-weave codegen, `src/compiler/35.semantics/aspect_weave.spl`).

## Symptom

`compiler.backend.backend.interpreter.InterpreterBackendImpl.process_module`
(`src/compiler/70.backend/backend/interpreter.spl`) fails with:

```
semantic: invalid assignment: index assignment requires identifier or field
access as container
```

on the SIMPLEST possible two-function module -- no aspects, no weaving, no
special HIR shapes:

```
fn f(n: i64) -> i64:
    n + 1

fn main() -> i64:
    f(41)
```

## Isolation proof

Reproduced with three shrinking probes run via `bin/simple test` (binary:
Rust bootstrap seed, `bin/simple --version` prints the seed warning banner;
`readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`):

1. A single-function trivial program (`fn main() -> i64: 41 + 1`) through
   `InterpreterBackendImpl.new().process_module(hir)` -- PASSES.
2. `submit_impl`/`submit_view`/`main` (three functions, one call chain) --
   FAILS with the error above.
3. Minimal two functions, `f` and `main`, `main` calls `f` -- FAILS with the
   same error.

None of these probes import or reference `aspect_weave.spl`,
`aspect_registry.spl`, `aspect_validation.spl`, or `join_point_model.spl` --
the defect is in the interpreter backend itself, pre-existing on `main`,
unrelated to the C3 AOP weave work that surfaced it.

## Where the error originates

The message is emitted by the Rust seed's OWN tree-walking interpreter
(`src/compiler_rust/compiler/src/interpreter/node_exec.rs:1453`, the
`else` branch of the index-assignment handler --
`ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT)
.with_help("index assignment requires an identifier or field access as the
container")`). That means the seed, while tree-walking the pure-Simple
SOURCE of `InterpreterBackendImpl` itself (`interpreter.spl`), hits an
index-assignment expression shape it does not support, somewhere in the
call-argument / call-frame setup path that only executes when a function
body contains a call to another user-defined function. Not yet narrowed to
an exact `interpreter.spl` line/callsite -- the two- and three-function
probes bracket it to "any code path taken only when evaluating a `Call` to a
non-builtin, user-defined function", but the exact statement was not
isolated (see "Next steps").

## Impact on the C3 weave spec

`test/01_unit/compiler/semantics/aspect_weave_spec.spl` has 5 examples:
2 pass (structural: `weave_forward_advice` inserts exactly one advice call,
write-back propagates to the caller's `Dict<text, HirModule>`, and a second
pass is idempotent). The remaining 3 -- all of which need to construct an
`InterpreterBackendImpl` and call `process_module` to prove the woven advice
call actually EXECUTES (the `1/0` tripwire design) -- fail on this defect
before reaching their own assertions. This is a genuine, currently
un-satisfiable precondition for those 3 examples; per `.claude/rules/
testing.md` ("a correct spec that fails is a legitimate artifact... leave it
RED") they were left failing rather than weakened or routed around.

## Next steps (not done here, out of scope for the C3 weave lane)

- Narrow to the exact `interpreter.spl` statement executed only on a
  user-function call (likely call-frame / local-env construction).
- Fix in `src/compiler/70.backend/backend/interpreter.spl` (pure Simple, not
  the Rust seed -- per `feedback_fix_spl_not_rust`).
- Re-run `aspect_weave_spec.spl`; examples 2-4 should go green once this
  underlying defect is fixed, with no changes needed to
  `aspect_weave.spl` itself.

---

## RESOLVED 2026-08-09 — root cause was `70.backend/backend/env.spl`, two defects

Fixed in `src/compiler/70.backend/backend/env.spl` (pure Simple; the Rust seed
was NOT touched). Two independent defects, both in `Environment`, both only
reachable once a second scope exists — i.e. inside a function call frame,
which is exactly why a single-function module passed and any user-to-user
call failed:

1. **Doubly-indexed assignment target.** `Environment.define` wrote
   `self.scopes[last_idx][name] = value`, and `Environment.assign` wrote
   `self.scopes[i][name] = value`. An index assignment whose CONTAINER is
   itself an `Index` expression is not a supported assignment target — the
   interpreter accepts only an identifier or a field access there — so
   evaluating `define` aborted with the reported
   `invalid assignment: index assignment requires identifier or field access
   as container` on the very first parameter bind of the callee. Rewritten as
   read-modify-write through a typed local (`var scope = self.scopes[i]` /
   `scope[name] = value` / `self.scopes[i] = scope`); the write-back is
   required because dicts/arrays are value types here.

2. **Descending inclusive range iterated zero times.** `Environment.lookup`
   and `Environment.assign` both searched inner scopes with
   `for i in (self.scopes.len() - 1)..=0:`. A descending `a..=b` (a > b) is
   an EMPTY range, so both loops ran zero iterations as soon as
   `scopes.len() > 1` — every lookup of a function parameter missed and fell
   through to globals, surfacing as `invalid operands for +` once defect 1
   was fixed. Rewritten as an explicit counted-down `while i >= 0` loop.
   These were the only two `..=0` ranges in `src/`.

### Verification (binary: Rust bootstrap seed `bin/simple`, which prints the
seed warning banner; compiler `.spl` edits are live on this interpreter path)

* Minimal repro (`fn f(n)` + `fn main(): f(41)`), plus a 3-function chain and
  a chain with an uncalled sibling function: 1/4 passed before, 4/4 after.
* `test/01_unit/compiler/semantics/aspect_weave_spec.spl`:
  `passed=2 failed=3` -> `passed=3 failed=2`. The example this bug directly
  blocked — *"the woven advice call actually EXECUTES: the tripwire fires"* —
  now passes.
* Sabotage: reverting `env.spl` to its pre-fix content reproduced exactly
  `passed=2 failed=3` on the weave spec and `passed=1 failed=3` on the repro;
  restoring it returned both to the numbers above.
* Regressions, all unchanged or green:
  `backend/interpreter_mode_spec` 4/4, `backend/interpreter_strict_mem_spec`
  9/9, `backend/jit_interpreter_spec` 8/8,
  `semantics/aspect_join_point_spec` 10/10, `semantics/const_eval_spec` 2/2,
  `semantics/call_graph_spec` 1/1. `backend/interpreter_backend_spec` is
  `passed=9 failed=2` both WITH and WITHOUT the fix — those 2 are
  pre-existing and unrelated.

### Still open (separate defects, NOT this bug)

* The remaining 2 `aspect_weave_spec` failures ("does NOT weave ... wrong
  join-point kind" / "... unmatched selector") are a DIFFERENT defect.
  Probing `process_module` directly on the byte-identical `SRC_WRONG_KIND`
  source returns Ok, so the failure is introduced somewhere in the spec's
  `weave_forward_advice(modules)` / `Dict<text, HirModule>` round-trip, not
  in the interpreter backend. Needs its own bug.
* `Environment.pop_scope` (`env.spl:119-121`) calls `self.scopes.pop()` and
  DISCARDS the result. Arrays are value types, so the pop is a no-op and
  call-frame scopes are never actually torn down. Left unchanged here to keep
  this fix scoped; worth its own bug + fix.
