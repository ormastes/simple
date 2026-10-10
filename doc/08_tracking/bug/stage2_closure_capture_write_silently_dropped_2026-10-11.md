# Stage2 native: a closure write to a captured local compiles and is silently dropped

- Date: 2026-10-11
- Found by: seed/stage-2 differential corpus, case `diff_closure_capture_mutation`
  (llvm and cranelift rows both DIFF: seed refuses rc=1, stage-2 builds and
  prints `flag=false counter=0`).
- Class: stage-2 accepts invalid code and emits wrong output, no diagnostic.
- Status: PARTLY FIXED on `work/rel-closure-capture-write-20261011`. Closures inside a
  `fn` body fail closed; closures in module-level statements (including
  `describe`/`it` blocks) and the paths under "Still open" do not.

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
| module-level `var` declared before the function (also when the enclosing fn assigns it first) | accepted, visible |
| module-level `var` declared after a function that assigns it | compile error |
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
2. `parse_and_build_module_with_scope_owner`
   (`_FlatAstBridge/module_assembly.spl`) calls it BEFORE
   `desugar_collections`, which rewrites `x = x + y` into `x.merge(y)` and
   erases the assignment. The error goes through the parser error channel the
   driver already poisons a module on (`par_had_error_get`), at the write's own
   position (`parser_error_at`), not the end-of-file token.
3. An error parse is never stored in the parse cache. A blob stored at a
   permissive level, or produced by a compiler without the check (phase-2
   import through `80.driver/cache/phase_compatibility_admission.spl`, which
   copies blobs and parses nothing; the shared parse store), is re-checked in
   `build_module_from_flat_pool_blob`: a hit that carries a captured write is
   treated as a miss, so the fresh parse reports it. That re-check sees the
   post-desugar tree, so it cannot see an `x = x + y` write.
4. Checker gaps against the seed, closed because the native lane now depends
   on it:
   - no module frame: an enclosing fn assigning a module global (`G = 0`)
     implicitly declared `G` local, so a closure writing the same global was
     REJECTED although the seed accepts it (shape of
     `src/compiler/90.tools/aop_proceed.spl:248`). Globals are now collected in
     declaration order, as in the seed: a `var G` declared AFTER the function
     is still rejected;
   - a destructuring `val`/`var (a, b) = ...` registered the literal name
     `"(a, b)"`, so a closure-local `a` was reported as a capture (false
     positive, found in review);
   - no descent into `match` / `if val` arms, so a write or a closure inside
     one was MISSED (`if val` desugars to a match).

Backend-neutral (flat AST, before HIR); nothing target specific. Cost,
interpreted: 1.6-1.9% of the parse of the same module
(`hir_lowering/statements.spl`: parse 22.9 s, check 0.37 s).

## Level switch

`SIMPLE_CAPTURE_WRITE_CHECK=error|warning|off`. Unset or unknown: `error`.
`warning` prints `[capture_write_check] warning: <path>: line N: <text>` and
compiles as before (the write is dropped); `off` skips the walk. The checker
is not proven to be a subset of the seed's, so this is the escape if it ever
rejects a module of the bootstrap closure.

## Declaration forms audited (closure-local, enclosing fn has the same name)

Seed accepts all of these; so does the checker (one spec example each):
`var (a, b) =`, three-element tuple, `val (a, b)` shadowed in a nested
closure, `for (a, b) in`, `for i, a in`, `case (a, b):`, `case Rect(a, b):`,
`case Point(x: a, y: b):`, `case Some(a):`, `if val a =`,
`if val Some((a, b)) =`, `while val a =`, `with e as a:`, lambda parameters.
The language has no `catch` form. Two shapes the pure-Simple parser itself
rejects, so the checker never sees them (seed accepts both; separate parser
gaps): `for (i, (a, b)) in` and `var Some(a) = e else:`.

## Parity with the seed

- Stricter than the seed, deliberately (the seed accepts these and loses the
  write, `c=0`; it is the same wrong code): a writing closure under an index
  expression `f(\x: ...)[0]`, under `??`, and a captured write in a `with`
  body.
- More lenient than the seed: a closure writing an `it`/`describe`-block `var`
  at module level (seed rejects; the checker walks `fn` declarations only).
- Missed by both: a captured write in a `defer` body and a tuple assignment
  `(c, d) = pair()`.

## Sites in the compiler's own closure

Text scan of every tracked `.spl` under `src/compiler`, `src/lib`, `src/app`
(14,069 files): 77 assignments to a bare identifier inside a lambda / nested
fn body within a `fn`, in 37 files. The checker run in process over those
files: **0 captured writes** (9 of the 37 do not parse cleanly in the
parse-only harness; the reviewer read those by hand: 0). Textual look-alikes
that are module-global writes (legal): `src/compiler/90.tools/aop_proceed.spl:248`,
`src/compiler/test/simple_coverage_test.spl:392,401`,
`src/app/interpreter/lazy/lazy_seq_spec.spl:272,284`,
`src/app/interpreter/lazy/lazy_val_spec.spl:54,89,293,297`,
`src/lib/{nogc_sync_mut,nogc_async_mut}/examples/testing/smoke_test_example.spl:65`.

So no stage-2-built compiler carries this wrong code in its own sources, and
the new error rejects nothing that compiles today. The seed already runs its
checker on every module it native-builds.

Real sites, all in one spec file outside the bootstrap closure:
`src/app/interpreter/perf/perf_spec.spl:306, 314, 322, 397` (closures writing
an `it`-block `var`). The seed rejects that file; the checker does not see
these (module-level statements).

## Still open (fail-open)

- Closures in module-level statements, including `describe`/`it` blocks.
- `defer` bodies, tuple assignment targets, and any expression form the walk
  does not descend into ("can miss a write but never invents one").
- Parse entries that do not run the check:
  `src/compiler/10.frontend/core/compiler/driver.spl`
  (`core_frontend_parse_reset` / `_append`, the core C-codegen driver), and the
  interpreter's imported-module loaders
  (`core/interpreter/module_loader_core.spl`, `module_loader_lazy.spl`): the
  interpreter checks the entry module only. The checker walks the whole decl
  arena, so calling it per appended module would be quadratic; not done.
- Colon-blocks are scopes, not closures (`language.md:23`) and may write an
  enclosing `var`. Whether the native pipeline writes those back was NOT
  examined.

## Specs

- `test/01_unit/compiler/50.mir/closure_capture_write_spec.spl`: 19 examples.
  Release tip `03ceb7f6408`: 11 of the first 14 fail. Now 19/19.
- `test/01_unit/compiler/50.mir/closure_capture_write_forms_spec.spl`: 32
  examples (14 declaration forms, 8 writes under binding constructs, 3
  stricter-than-seed, 1 position, 6 level switch / cache hit). 7 failed at
  the first fix commit (`33dd836c9fe` after rebase; reviewed as `e544d6c2d44`).
  Now 32/32.
- `test/01_unit/compiler/interpreter/nested_fn_enclosing_var_mutation_spec.spl`
  (shared checker, interpreter side): 7/7.
