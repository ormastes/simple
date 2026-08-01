# `bin/simple test`: a wildcard-imported `main` adds a phantom file-level failure

**Date:** 2026-08-01
**Component:** `bin/simple test` outer/second pass (test runner + module loader)
**Severity:** **false RED across the suite** — affected spec files report one extra
failure that no example produced. Example pass counts stay correct, so this
inflates the failing-FILE count only. A fail-*closed* error, but a phantom one:
it makes green work look broken and hides real regressions in the noise.

## Symptom

A spec whose import graph **wildcard-imports** a module declaring a top-level
`fn main` reports an extra file-level failure AFTER all its examples pass:

```
error: semantic: type mismatch: cannot convert function to int
error: test-runner: spec failed
Results: 2 total, 1 passed, 1 failed
```

The error text varies with what occupies the colliding slot — `cannot convert
dict to int` in the original lint case, `function to int` in the minimal one.

## Minimal reproduction (verified twice, independently)

`src/probe/just_main.spl` — the entire file:

```
fn main():
    print("hello")
```

A one-assertion spec that does `use probe.just_main.*` → `2 total, 1 passed, 1 failed`.

Controls, all clean at `1 total, 1 passed, 0 failed`:

| variant | result |
|---|---|
| `use probe.just_main.*` (wildcard, fn named `main`) | **FAILS** |
| `use probe.just_notmain.*` (wildcard, fn renamed) | clean |
| `use probe.just_main.{main}` (**named** import of the same symbol) | clean |
| `compile` instead of `test`, same wildcard import | clean |

So all three of these are required: the **test** lane, a **wildcard** import, and
the imported symbol being literally named **`main`**.

### CORRECTION — the consumer's import style is NOT what matters

The table above measures the **direct** edge (spec → module). Do not generalize
"named import is clean" to the transitive case: it is false there, and reading it
that way sends you hunting for wildcard imports in specs, of which there are
**zero**.

Both real reproducers — `collection_easy_fix_spec.spl` and
`collection_index_mutation_spec.spl` — use a **named** import
(`use compiler.tools.lint.main.{Linter, lint_cli_source}`) and reproduce anyway.
The wildcard that matters is the one **inside the facade**:
`compiler.tools.lint.main` does `export use ..._LintMain.entry_and_fixes.*`,
which bakes `main` into the facade's own symbol table at load time regardless of
how a consumer imports from it.

Precise necessary condition: **a wildcard import/re-export anywhere in the
import chain pulls a top-level `main` into some module's symbol table.** The
consumer may import by name and still be affected.

Probe environment kept at
`scratchpad/lint_probe/` (`src/probe/just_main.spl`, `src/probe/just_notmain.spl`,
`test/probe_just_main_spec.spl`, `test/probe_just_notmain_spec.spl`,
`test/probe_named_main_spec.spl`).

## Where it happens

The runner is **two-phase**. An outer process spawns a child that actually
executes the spec; the child reports `1 example, 0 failures` — genuinely clean —
and exits. Only afterwards does the outer pass run (co-occurring with loading
`std.nogc_sync_mut.spec.env_detect`) and emit the error. `compile` never
reproduces it, so the defect is in the test runner's outer pass, not in the
compiler front end generally.

Leading hypothesis (not yet confirmed in code): the outer pass looks up a
module-level `main` to decide whether the module is executable / what its exit
status is, finds the **wildcard-imported** one rather than the module's own, and
type-checks it as `int` — `fn main() -> Int` returns a status code.

## Real-world instance

`src/compiler/90.tools/lint/main.spl:11` does
`export use compiler.tools.lint._LintMain.entry_and_fixes.*`, and
`_LintMain/entry_and_fixes.spl:231` declares `fn main() -> Int` — the lint CLI's
own entry point. So the CLI `main` leaks through the facade's wildcard
re-export into every consumer, and **every spec importing the lint facade**
inherits the phantom failure. That is how this was found; see
`lint_module_graph_spec_pollution_dict_int_2026-07-31.md` for the bisect that
got here.

Note this is also an API smell in its own right: a library facade should not
re-export a CLI entry point, independent of the runner defect.

## Blast radius (measured 2026-08-01, static)

Smaller than the 608 `fn main` declarations suggest, and concentrated in one
facade:

| axis | count |
|---|---|
| files under `src/` declaring a top-level `fn main` | 608 |
| wildcard import statements in `src/`+`test/` | 9,767 |
| **specs directly wildcard-importing a main-declaring module** | **0** |
| facades that `export use`-wildcard a main-declaring module | **5** |
| **spec files importing one of those 5 facades (any style)** | **29** |

The 5 facades: `compiler.tools.lint.main`, `app.cli.main`, `app.wm_compare.main`,
`compiler.tools.sffi_gen.main`, `os.port.bootstrap_cross`. No level-2 facade
re-exports any of them, so depth-1 is exhaustive.

`compiler.tools.lint.main` dominates at 37 importers (27 test + 10 src) —
roughly 10× every other facade. Fixing that one facade addresses ~27 of the 29.

Caveats stated by the measuring lane, kept deliberately: ~6 of the 29 are
duplicate-tree mirrors (`test/unit/**` mirrors `test/01_unit/**`) and 5 more are
paired `.spipe_matchers_*` shadow files, so distinct authored specs are closer to
**~18** — but if the runner executes both mirror trees, executed impact is
higher. Matching on module BASENAME instead of full dotted path yields 7 direct
hits, and **all 7 are false positives** (e.g. `compiler.visibility` vs the
main-declaring `compiler.tools.verify.visibility`); use exact-path joins.

`doc/08_tracking/test/test_result.md` **cannot** corroborate this: it was
generated 2026-05-19, predates the bug's discovery, and reports example
granularity (120,809 examples) with no file-level summary — so it structurally
cannot show an "examples green, +1 phantom file failure" signature. No tracked
doc currently gives an authoritative file-level count to check against.

## How the bisect got here (so it is not repeated)

Two whole hypothesis classes were eliminated first, and both are dead ends:

- **Not a lint bug.** With the `_LintMain` import cycle genuinely broken in a
  disposable copy, all six submodules loaded clean individually. The family is
  innocent.
- **Not any single declaration.** All 22 external dependencies are clean
  imported in isolation, and the only module-level Dict in the family uses the
  safe `contains_key` pattern.
- **Per-file bisection is impossible as written** — all six `_LintMain`
  submodules `use compiler.tools.lint.main.*` themselves, so importing any one
  drags the family back in. An earlier "all six reproduce individually" result
  was a cycle artifact, NOT attribution.

## Next step

Locate the outer-pass code that resolves a module's `main` and make a
wildcard-imported `main` not count as the module's own entry point. Grep the
runner (`src/app/` test_runner_new) and `src/compiler/99.loader/` for
special-casing of the literal name `"main"` in wildcard-import/re-export
resolution.

## Lesson

**A phantom failure reported after a clean child run is a runner artifact, not a
code defect.** The examples had already passed in a separate process; anything
reported afterwards is bookkeeping. Check which phase emitted an error before
attributing it to the code under test — three sessions read this as a real
type error in the lint module graph.
