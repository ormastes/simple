# Importing a module named `main` adds a phantom test failure

**Date:** 2026-08-01
**Component:** `evaluate_module_impl`, `src/compiler_rust/compiler/src/interpreter_eval.rs`
**Severity:** **false RED across the suite** — 73 spec files report a failure no
example produced. Example counts stay correct; the failing-FILE count is
inflated, so real regressions hide in phantom noise.

> **Title history:** this was filed as a wildcard-import defect and twice
> re-scoped as evidence came in. Neither "the spec must wildcard-import" nor
> "the module must declare `fn main`" is true. The confirmed rule is below.

## The rule

**Importing any module whose final path segment is literally `main` — by name or
by wildcard — binds that module's entire export dict under the reserved key
`"main"`, which the runner later forces through `.as_int()`.**

The module does **not** need to declare `fn main`. The importer's style does
**not** matter. Only the last segment of the imported path matters.

```
error: semantic: type mismatch: cannot convert dict to int
error: test-runner: spec failed
Results: 2 total, 1 passed, 1 failed
```

## Control matrix (each verified on the seed binary)

`probemain/main.spl` and `probemain/notmain.spl` have **identical content** and
contain **no `fn main`**:

```
fn helper() -> Int:
    42
```

| spec import | result |
|---|---|
| `use probemain.main.{helper}` — file named `main.spl` | **FAILS** `cannot convert dict to int` |
| `use probemain.notmain.{helper2}` — identical, renamed file | clean |
| `use probe.just_main.*` — wildcard, file declares `fn main` | **FAILS** `cannot convert function to int` |
| `use probe.just_notmain.*` — wildcard, fn renamed | clean |
| `use probe.just_main.{main}` — named import of the `main` symbol | clean |
| `compile` instead of `test`, any of the above | clean |

The two distinct error texts correspond to two distinct sites (below), which is
the strongest evidence that the mechanism is understood rather than guessed.

**Independent confirmation from the opposite direction:** a separate lane removed
`fn main` from the lint graph completely — replaced the facade's
`export use ..._LintMain.entry_and_fixes.*` with an explicit 10-symbol named
list, AND renamed `fn main() -> Int` to `lint_main()` in `entry_and_fixes.spl`.
With **zero** `fn main` anywhere in the reachable chain, all three lint specs
still failed identically. That is exactly what the rule predicts: the file is
still `.../lint/main.spl`, so site B still binds its export dict under `"main"`.
Removing the *function* cannot help; only renaming the *file* or fixing the
runner can.

## Root cause — two compounding sites

Both in `evaluate_module_impl`, `src/compiler_rust/compiler/src/interpreter_eval.rs`.

**Site B — the dominant one (`dict to int`).** `binding_name` for
`ImportTarget::Glob | ImportTarget::Group(_)` is derived from
`use_stmt.path.segments.last()` — the last **path segment**, independent of which
symbols are named. For `use compiler.tools.lint.main.{Linter, lint_cli_source}`,
`binding_name == "main"` purely because the file is `.../lint/main.spl`. Then,
unconditionally and outside any per-target guard,
`env.insert(binding_name, value)` binds the whole module — a `Value::Dict` of
its exports — under the reserved key `"main"`.

**Site A — the narrower one (`function to int`).** In the `ImportTarget::Glob`
per-export loop, `functions.insert` was already guarded by `if name != "main"`,
but the following `env.insert` and `MODULE_GLOBALS` insert were **not**. So a
glob-imported `fn main` still landed in the importer's scope.

**Shared consumption point.** The runner does
`env.get("main").cloned().unwrap_or(Value::Int(0))` … `.as_int()?` — a
"fall back to a `main = <value>` binding" convention with no type discrimination.
Anything that ends up in `env["main"]` is forced through `.as_int()`.

## Why it fools people

The runner is **two-phase**. A child process executes the spec and reports
`0 failures` — genuinely clean — and exits. Only afterwards does the outer pass
emit the error. **Anything reported after a clean child run is runner
bookkeeping, not the code under test.** Three sessions read this as a real type
error in the lint module graph.

## Blast radius (measured 2026-08-01)

| | |
|---|---|
| **spec files importing a module path ending in `.main`** | **73** |
| `src/` files doing the same | 31 |

Top imported `.main` modules: `app.mcp.main` (41), `compiler.tools.lint.main`
(37), `compiler.tools.fix.main` (11), `std.scv.main` (5),
`compiler.tools.duplicate_check.main` (5), `app.dashboard.main` (5).

Superseded earlier estimate: an count of 29 built on "facades that
wildcard-re-export a `fn main`" measured the wrong population — that framing
missed every `.main` module that declares no `fn main`, and `app.mcp.main`
(the single biggest offender) was absent from it entirely.

`doc/08_tracking/test/test_result.md` cannot corroborate this: generated
2026-05-19, example granularity (120,809 examples), no file-level summary — it
structurally cannot show an "examples green, +1 phantom file failure" signature.

## Fix

A patch exists but is **UNVERIFIED** — it could not be built. Two hunks in
`evaluate_module_impl`: skip binding a glob-imported `main` function into
`env`/`MODULE_GLOBALS` (site A), and skip the module-dict bind when
`binding_name == "main"` was derived from the path for a `Glob`/`Group` target
(site B). `Single`/`Aliased` imports are deliberately untouched — there the local
name is explicitly chosen by the user, not derived from the path.

This is **Rust-only** logic in the seed interpreter/module loader, with no
exercised `.spl` equivalent, so the repo's fix-the-`.spl`-not-the-Rust rule does
not offer an alternative here. Verification is blocked on seed build contention
(six concurrent `simple-driver` builds produced
`ld terminated with signal 7 [Bus error]`).

**To verify when contention clears:** one clean seed build, then re-run the six
control-matrix cases plus the three real lint specs
(`collection_index_mutation_spec` 6 ex, `collection_array_rebuild_spec` 5 ex,
`collection_easy_fix_spec` 4 ex) — each currently carries the phantom failure and
must lose it while the controls stay clean.

Probe environment kept at `scratchpad/lint_probe/` (`src/probemain/main.spl`,
`src/probemain/notmain.spl`, `src/probe/just_main.spl`, `src/probe/just_notmain.spl`
and the matching specs under `test/`).

## Dead ends — do not re-run

- **Not a lint bug.** With the `_LintMain` import cycle broken in a disposable
  copy, all six submodules loaded clean individually.
- **Not any single declaration.** All 22 external dependencies are clean in
  isolation; the only module-level Dict in the family uses the safe
  `contains_key` pattern.
- **Per-file bisection is meaningless** while a family's members mutually import
  their own facade — every file "reproduces" via the cycle.
- **Basename joins over-report.** Matching module basenames instead of exact
  dotted paths gave 7 direct hits, all false positives.

## Lesson

Each of the three framings was consistent with all evidence available when it
was written, and each was wrong. What broke the cycle was building a control
that differed in exactly **one** attribute: two files with byte-identical
contents, one named `main.spl` and one named `notmain.spl`. The name was the
variable nobody had isolated, because it was never the thing under suspicion.
When a hypothesis keeps surviving in weakened form, test the attribute you have
been treating as incidental.
