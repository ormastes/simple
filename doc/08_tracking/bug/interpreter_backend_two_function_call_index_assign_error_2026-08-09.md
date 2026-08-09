# InterpreterBackendImpl.process_module fails on ANY module with a user-to-user function call

Status: OPEN (RED, blocking)
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
