# Stage2 native: a closure write to a captured local compiles and is silently dropped

- Date: 2026-10-11
- Found by: seed/stage-2 differential corpus, case `diff_closure_capture_mutation`
  (llvm and cranelift rows both DIFF: seed refuses rc=1, stage-2 builds and
  prints `flag=false counter=0`).
- Class: stage-2 accepts invalid code and emits wrong output, no diagnostic.
- Status: FIXED on `work/rel-closure-capture-write-20261011` (fail closed).

## Language rule (the seed is the oracle)

Owner ruling 2026-09-27, `.claude/rules/language.md:22`: a nested `fn` or
lambda captures enclosing locals BY VALUE and READ-ONLY. A write is a compile
error, not a by-reference update. Probed with `seed run`:

| shape | seed |
|-------|------|
| `fn():` lambda assigns an enclosing `var` (plain or `+=`) | compile error |
| closure in a `for` body writes an outer `var` | compile error |
| closure that escapes (returned) writes its definer's local | compile error |
| closure nested in a closure writes the outermost local | compile error |
| nested `fn` declaration writes an enclosing local | compile error |
| `\x:` block lambda argument writes an enclosing local | compile error |
| write under `while`/`for`/`if val`/`match` inside the closure | compile error |
| rebinding a captured collection (`xs = [7]`) | compile error |
| field / index write through a captured reference (`b.n = ..`, `xs[0] = 9`, `d["k"] = 2`) | accepted, visible outside |
| closure-local `var`, parameter, shadowing `var` | accepted |
| module-level `var` (also when the enclosing fn assigns it first) | accepted, visible |
| read of a captured `var` reassigned after the closure was made | by-value: old value |

Diagnostic (one text for every engine):
`cannot assign to captured variable `<name>` inside nested fn `<f>` (line N): closures capture enclosing locals by value and are read-only; return the new value or use a module-level `var``
(`inside a closure` for an anonymous lambda).

## Root cause

The check existed in two of three engines only:

- seed: `src/compiler_rust/parser/src/capture_write_check.rs`, called from
  `pipeline/module_loader.rs:2386` and `pipeline/native_project/compiler.rs:684`;
- pure-Simple interpreter: `capture_write_check_module`, called from
  `src/compiler/10.frontend/core/interpreter/mod.spl` (`core_interpret`);
- pure-Simple NATIVE pipeline: never called.
  `parse_and_build_module_with_scope_owner`
  (`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`) went
  parse -> desugar -> `flat_ast_to_module` with no semantic gate.

MIR then does what the rule says for READS: `snapshot_lambda_capture`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:4838`)
copies each free variable into a frozen temp at bind time and the body is
lowered against that copy, so an assignment in the body targets the copy. In
process, release tip `03ceb7f6408`: the fixture lowers with 0 parse, 0 HIR and
0 MIR errors (`closure_capture_write_spec.spl`, first example).

## Fix

1. The checker moved out of the interpreter into
   `src/compiler/10.frontend/core/capture_write_check.spl` so both pure-Simple
   engines share it (no interpreter import in the bootstrap closure).
2. `parse_and_build_module_with_scope_owner` calls it BEFORE
   `desugar_collections` and reports through `parser_error`, the channel the
   driver already poisons a module on (`par_had_error_get`). Before, not
   after: `desugar_collections` rewrites `x = x + y` into `x.merge(y)` and
   erases the assignment. An error parse is never stored in the parse cache,
   and the cache scope folds the compiler source fingerprint, so a cache hit
   cannot bypass the check.
3. Two gaps of the shared checker against the seed, closed because the native
   lane now depends on it:
   - it had no module frame: an enclosing fn assigning a module global
     (`G = 0`) implicitly declared `G` local, so a closure writing the same
     global was REJECTED although the seed accepts it (false positive; shape of
     `src/compiler/90.tools/aop_proceed.spl:248`);
   - it did not descend into `match` / `if val` arms, so a write or a closure
     inside one was MISSED (`if val` desugars to a match).

Backend-neutral (flat AST, before HIR); nothing target specific. Cost,
interpreted: 1.6-1.9% of the parse of the same module
(`hir_lowering/statements.spl`: parse 22.9 s, check 0.37 s).

## Sites in the compiler's own closure

Scan of every tracked `.spl` under `src/compiler`, `src/lib`, `src/app`
(14,069 files): 77 assignments to a bare identifier inside a lambda / nested
fn body, in 37 files. The fixed checker run in process over those 37 files
(plus the inline-lambda file below): **0 captured writes**. All 77 target a
closure-local, a parameter or a module global. Three look like captures
textually and are module-global writes (legal):
`src/compiler/90.tools/aop_proceed.spl:248`,
`src/lib/nogc_sync_mut/examples/testing/smoke_test_example.spl:65`,
`src/lib/nogc_async_mut/examples/testing/smoke_test_example.spl:65`.

So no stage-2-built compiler carries this wrong code in its own sources, and
the new error rejects nothing that compiles today. The same holds from the
other side: the seed already runs its checker on every module it native-builds.

One real site outside the bootstrap closure:
`src/app/interpreter/perf/perf_spec.spl:314,322`
(`.with_setup(\: setup_called = true)` writing an `it`-block `var`). The seed
fails that file at parse (`expected expression, found Assign`); it is a spec,
not compiler input.

## Fail closed, and what is still open

- Every write of a captured local the checker sees is a compile error;
  nothing is supported by-reference (that would contradict the ruling).
- The walk "can miss a write but never invents one": expression forms that do
  not carry statements are not descended into. Not covered: a closure or write
  inside a module-level statement (outside any `fn`), and an expression-bodied
  lambda whose body is an assignment at module level (the perf_spec shape).
- Colon-blocks (`describe`/`it`/hooks) are scopes, not closures
  (`language.md:23`) and may write an enclosing `var`. Whether the native
  pipeline writes those back was NOT examined here.

## Specs

`test/01_unit/compiler/50.mir/closure_capture_write_spec.spl`: 19 examples.
Release tip: 3 pass, 11 fail of the first 14 (every reject shape red). After
the fix: 19/19. `test/01_unit/compiler/interpreter/nested_fn_enclosing_var_mutation_spec.spl`
(shared checker, interpreter side): 7/7.
