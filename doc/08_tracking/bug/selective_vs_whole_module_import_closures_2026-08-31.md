# `use M` vs `use M.{x}`: two independent defects, not one (2026-08-31)

Investigates the convergence of PR #182's `Dict` cluster ("`use M` compiles clean
but `use M.{x}` fails — they build different closures") and PR #183's R2/R3
("`use m.{X}` where `m` does not provide `X` is silently erased to ANY").

**Verdict: TWO independent defects. Neither is "selective imports resolve
differently from whole-module imports."** Both halves of the shared hypothesis
are refuted by fixture, below.

Seed built from `origin/main` @ `46f15eae6ff` in an isolated worktree,
`CARGO_TARGET_DIR=/mnt/data/cargo-targets-imports2`. Every rc read into a
variable on the line after the invocation, never through a pipe.

## Defect A — ANY-erasure is import-independent (refutes Finding 2's framing)

`fx/a.spl` (**no import at all**) and `fx/b.spl` (`use m.{Ghost}` where `m.spl`
declares only `Real`) produce a **byte-identical** diagnostic:

```
=== a rc=1
HIR lowering: Unsupported feature: cannot infer field type while lowering probe: struct 'ANY' field 'w0'
=== b rc=1
HIR lowering: Unsupported feature: cannot infer field type while lowering probe: struct 'ANY' field 'w0'
```

The import is incidental. The mechanism is the general unknown-type fallback:

- `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:294-297` — under
  `lenient_types`, an unresolvable *type* name returns `TypeId::ANY` instead of
  `LowerError::UnknownType`.
- `src/compiler_rust/compiler/src/hir/lower/lenient_global_diag.rs:1-52` — the
  sibling fallback for unresolvable *identifiers* (→ `HirExprKind::Global`), with
  the architectural reason already documented in its header: `native_project`'s
  `lower_file` lowers **one file at a time** and `self.globals` holds only the
  current AST module's items, so a legitimate cross-file reference is
  *necessarily* unresolvable at HIR time. "Erroring here would break all
  cross-module compilation."
- `lenient_types` is set unconditionally at all four HIR entry points:
  `hir/lower/mod.rs:195`, `hir/lower/mod.rs:213`, `pipeline/execution.rs:1013`,
  `pipeline/native_project/compiler.rs:664`.

**There is no warning to flip on the compile path.** The `[use-warning]` oracle
(`interpreter_module/module_loader.rs:489,516`) is called only from
`interpreter_module/module_loader.rs:888,1250` — the interpreter loader, which
"reports only; the loader still registers the module's whole surface." No
`pipeline/` or `hir/lower/` code path consults it. Making unsatisfied selective
imports a hard error is therefore not a warning-to-error flip; it requires
whole-program (not per-file) lowering. Owner decision.

## Defect B — single-segment relative `use p` binds nothing (contained)

`use p` where `p.spl` sits beside the importer is a **no-op**: it binds neither
bare names nor a `p.` namespace, and — critically — never loads the module's
closure, so a module containing a hard error still compiles green.

```
# p.spl: pub fn boom() -> i64: return totally_undefined_symbol_xyz()
use p                 -> rc=0   (module never loaded — vacuous)
use p.{boom}          -> rc=1   Undefined("undefined identifier: totally_undefined_symbol_xyz")
use p / p.only_in_file() -> rc=1 Undefined("undefined identifier: p")
```

**This is the whole of Finding 1, and it is contained to the single-segment
form.** With a dotted path the two forms are identical:

```
# d/p.spl carries the same error
use d.p               -> rc=1   Undefined("undefined identifier: totally_undefined_symbol_xyz")
use d.p.{boom}        -> rc=1   Undefined("undefined identifier: totally_undefined_symbol_xyz")
```

So `use M` and `use M.{x}` do **not** build different closures for dotted module
paths, which is every real stdlib/app import. PR #182's probes were dotted and
were therefore **not** vacuous; its `Dict` cluster is not explained by this.
Population of the affected form: **259** single-segment bare `use M` statements
and 351 single-segment `use M.{...}` across `src/` + `test/`.

Not fixed here: no failing real-code repro exists, and the fix (make bare `use M`
bind the module's surface or a namespace) is a semantic change over 22,778 bare
`use M` statements in 16,103 files. Owner decision.

## Blast radius — if unsatisfied selective imports became an error

Static census over `src/` + `test/` (excluding `vendor/`), counting a name as
provided when the target module defines it, re-exports it in an `export use
{...}` **or** a plain `use ...{...}` group (shim modules re-export those), and
skipping modules with glob or bare whole-module `export use` as opaque:

| metric | count |
|---|---|
| group-import statements scanned | 69,381 |
| statements with >= 1 unprovided name | **1,383** |
| unprovided (name, site) pairs | **3,351** |
| distinct importer files affected | **1,102** |

Both error directions are stated rather than hidden. **Undercount:** 27,960
statements name a module this scanner could not resolve and are excluded
entirely. **Overcount:** generated surface the regexes cannot see (constructor
`Type__new` forms are compensated for; other generated surface is not).

**Recommendation: do not flip.** Even at the low end this fails > 1,000 files,
and on the compile path there is no warning to flip in the first place. The
tractable increments, in order: (1) call the existing `[use-warning]` oracle from
the compile path so the diagnostic names the bad import and module instead of
surfacing as `struct 'ANY' field '<f>'` far away; (2) drive the census to zero
under a ratchet, as `check-unbacked-extern-ratchet.shs` does for externs;
(3) only then consider strictness.

## Also observed, not acted on

`pipeline/module_loader.rs:24-38` carries a **coarse** copy of
`prefer_package_init_for_member_import`: it redirects any `Group`/`Glob` import
from `X.spl` to a sibling `X/__init__.spl` unconditionally, lacking both the
per-name probe and the load-stack cycle guard that
`interpreter_module/module_loader.rs:577-617` grew for exactly this hazard.
32 file+package pairs exist under `src/lib`. A fixture with the pair present did
**not** reproduce a failure, so this is a latent divergence between the two
loaders, filed rather than "fixed" without a repro.

## Not done
No test, assertion or gate was weakened, skipped or deleted. No Rust changed.
