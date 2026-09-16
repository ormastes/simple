# `use M` vs `use M.{x}`: two independent defects, not one (2026-08-31)

Investigates the convergence of PR #182's `Dict` cluster ("`use M` compiles clean
but `use M.{x}` fails — they build different closures") and PR #183's R2/R3
("`use m.{X}` where `m` does not provide `X` is silently erased to ANY").

**Verdict: TWO independent defects.** Finding 2's framing is refuted by fixture
(Defect A is import-independent). Finding 1 is CONFIRMED, on the real module,
with a mechanism of its own (Defect B: a whole-module `use M` does not load a
package's closure). They share no mechanism.

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

## Defect B — whole-module `use M` does not load a PACKAGE's closure

**CORRECTED 2026-08-31 after probing the real module.** An earlier revision of
this doc scoped this to the single-segment relative form. That was wrong: the
discriminating variable is **package vs file**, not segment count.

`use M` is a no-op — it binds neither bare names nor an `M.` namespace, and never
loads the module's closure, so a module containing a hard error still compiles
green — whenever `M` resolves to a package (`M/__init__.spl`), and also for the
single-segment relative file form. Dotted *file* imports are unaffected.

| module shape | `use M` | `use M.{x}` |
|---|---|---|
| single-segment file (`p.spl`) | **rc=0 vacuous** | rc=1 loads |
| dotted file (`d/p.spl`) | rc=1 loads | rc=1 loads |
| dotted package (`d/pkg/__init__.spl`) | **rc=0 vacuous** | rc=1 loads |

Fixture, identical `__init__.spl` body carrying `totally_undefined_symbol_xyz()`:

```
use d.pkg           -> rc=0
use d.pkg.{boom}    -> rc=1   Undefined("undefined identifier: totally_undefined_symbol_xyz")
```

`use p` / `p.only_in_file()` additionally gives `Undefined("undefined identifier: p")`,
so no namespace is bound either.

**This reproduces on the real module from PR #182.** `std.gc_sync_mut.db` is
package-only (`db/__init__.spl`, no `db.spl`), and at `46f15eae6ff`:

```
use std.gc_sync_mut.db        -> rc=0   (module never loaded)
use std.gc_sync_mut.db.{...}  -> rc=1
```

So **Finding 1 is real** and its mechanism is this, not the ANY-erasure of
Defect A. It also means every `use M` probe against a package module in the
PR #163 / #182 investigations was **vacuous** — a green from such a probe is not
evidence the module's closure is clean. That invalidates a class of prior
"probes clean" evidence, including PR #182's "`std.gc_sync_mut.db` and
`db.dbfs_engine` both probe clean".

Population floor: **42** bare `use M` statements resolve to a package under a
scanner that handles only `std.`-rooted and `src/`-relative paths; 560 resolve to
a file (unaffected) and 22,187 use roots the scanner cannot resolve, so 42 is a
floor, not the population.

Not fixed here: the fix (make a whole-module `use M` load and bind a package's
surface) is a semantic change whose true population is unmeasured, and would
newly surface every latent error in those closures — the same class of decision
as the blast radius below. Owner decision.

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
