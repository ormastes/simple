# Bug: nested-block `var` redeclaration leaks into outer scope (Rust seed interpreter)

- **Date:** 2026-07-17
- **Status:** open (found incidentally; not fixed in this pass)
- **Area:** `src/compiler_rust` interpreter fallback (tree-walking `Env`)

## Symptom

Discovered while verifying the fix for
`doc/08_tracking/bug/local_var_kernel_shadowed_by_module_2026-07-06.md`. A
`var` re-declared with the same name inside a nested block (`if`/`for` body)
does not restore the outer binding once the nested block exits — the inner
value leaks out.

## Minimal repro

```simple
fn run(args: [text]) -> i32:
    var kpath = "outer"
    for arg in args:
        if arg.starts_with("x"):
            var kpath = "inner"
            print "nested={kpath}"
    print "outer_after={kpath}"
    0

fn main() -> i32:
    run(["xyz"])
```

Actual output (Rust seed, `bin/simple run`, interpreter fallback):
```
nested=inner
outer_after=inner
```

Expected: `outer_after=outer` — the outer `kpath` binding should be restored
once the `if` block's own `kpath` goes out of scope.

## Root cause (suspected, not confirmed)

`compiler_rust`'s tree-walking interpreter fallback binds locals into a flat
`Env` (name -> value map, see
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs::bind_let_pattern_element`)
with no block-scope stack: entering a nested block does not snapshot/restore
prior bindings for names that get redeclared inside it. This is distinct from
the `kernel`-keyword bug (which was a parser mis-capitalization) — this one
reproduces with an ordinary, non-keyword name. Not root-caused further or
fixed here; scope of this lane was the kernel/module shadowing bug only.

## Verification

Confirmed reproducing at commit `985885cb314` in
`/home/ormastes/dev/wt_q_optdyn` via `bin/simple run` (Rust seed interpreter
fallback path). Not yet checked against the pure-Simple self-hosted
interpreter/compiler (`src/compiler/`).

The exact source repro is preserved as ignored Rust regression
`test_nested_block_var_redeclaration_restores_outer_binding` in
`src/compiler_rust/compiler/tests/interpreter_coverage_line.rs`; remove the
ignore when block scopes restore shadowed bindings.
