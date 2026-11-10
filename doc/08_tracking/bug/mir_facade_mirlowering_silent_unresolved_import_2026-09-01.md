# `use compiler.mir.{MirLowering}` resolves silently, then fails at the use site

- **Filed:** 2026-09-01
- **Status:** SUPERSEDED (silent-unresolved-import defect mitigated at tip; verified 2026-11-11, lane p3-compiler4). The reported blocker "`MirLowering` not
  found — `compiler.mir` fails to re-export `MirLowering`" is **NOT a defect**;
  see "Not a bug" below.
- **Platform:** cross-platform. **Explicitly NOT Windows-specific** — see
  "Unix asymmetry hypothesis: REFUTED".
- **Seed:** `src/compiler_rust/target/release/simple.exe`,
  md5 `286f66b8615dce0e0da788f0550c4008`
- **HEAD:** `04603e026ca` (detached), 18866 dirty paths in a shared worktree

## Not a bug: the facade omission is deliberate and documented

`src/compiler/50.mir/__init__.spl` (module `compiler.mir`) deliberately does
**not** export `MirLowering`/`MirError`. The rationale is written in that file
at lines 145-177 and traced to
`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`:
re-exporting it drags `HirFunction` (via
`_MirLowering/function_lowering.spl:69`, `lower_function(fn_: HirFunction)`)
into the facade's lowering scope and reintroduces a Stage 3 self-host
`Effect` type conflict. The file states the resolution verbatim: "keep
`MirLowering`/`MirError` reachable only via the direct submodule path, which is
what every actual caller already used."

**Restoring the re-export will re-break the Stage 3 bootstrap. Do not do it.**

**The sanctioned path works today.** Measured:

| import | `MirLowering.new(nil)` | rc |
|---|---|---|
| `use compiler.mir.mir_lowering.{MirLowering}` | works, prints | **0** |
| `use compiler.mir.{MirLowering}` | `semantic: variable MirLowering not found` | 1 |

Both in-tree product consumers already use the sanctioned path —
`src/compiler/80.driver/pipeline_fn.spl:13` and
`src/app/simpleos_tool/focused_pipeline.spl:10`. A repo-wide grep for
`compiler.mir.{...MirLowering...}` finds **zero** call sites; the only hits are
the explanatory comments in `__init__.spl` itself. Nothing in the MCP
native-build lane is blocked by this.

## Unix asymmetry hypothesis: REFUTED

The hypothesis under investigation was that this is a Windows module-resolution
defect (path case or separators). It is not. The omission is a **source-level
export list** in a `.spl` file, byte-identical on every platform, landed
deliberately on 2026-08-06 with an in-file rationale. There is no
platform-conditional code on this path;
`src/compiler/99.loader/module_resolver/resolution.spl` performs no case
normalization at all, so the behaviour cannot differ by host filesystem
semantics here. No Unix/Windows asymmetry exists to exploit as a clue.

## The actual (secondary) defect

Importing a name a module does not export **succeeds silently**. Reproduction
from the repo root:

```sh
printf 'use compiler.mir.{MirLowering}\n\nfn main():\n    val m = MirLowering.new(nil)\n    print("x")\n' > probe.spl
src/compiler_rust/target/release/simple.exe run probe.spl; rc=$?
```

Observed (`rc=1`):

```
[CODEGEN-STUB-FALLBACK] body compilation failed for 'main':
  ModuleError("GlobalLoad: unresolved identifier 'MirLowering'
  (not a global, function, const-data name, or import)")
error: semantic: variable `MirLowering` not found
```

The import statement itself raises nothing. A module path that does not exist
at all *is* a hard error (`E1034`, "refusing to fall back to the interpreter"),
but a module that exists and simply does not export the requested **name** is
not checked. The failure is therefore deferred to the first use and reported as
an unbound *variable*, which names neither the import nor the module — exactly
the diagnostic that made this blocker look like a re-export failure.

This is the same diagnostic-quality class the resolver already fixed for
missing modules; it needs extending from module paths to imported item names.

**Expected:** `use M.{Name}` where `M` does not export `Name` is an import-time
error naming `M` and `Name`.

## Unblock condition

Emit an import-time diagnostic for unresolved item names in a resolvable
module. Wildcard re-export chains complicate this: `mir_lowering.spl:18-21`
re-exports via `export use compiler.mir._MirLowering.{...}.*`, and
`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:88,704`
records that "a wildcard import has no flattened item rows" — so the checker
must materialize wildcard chains before it can decide a name is genuinely
absent, or it will produce false positives on every wildcard re-export.

## Specs

`test/01_unit/bugs/mir_facade_mirlowering_import_spec.spl`

## Triage 2026-11-11 (p3-compiler4 lane, batch 4 row 6) — SUPERSEDED (silent-import defect mitigated at tip)

The secondary defect (importing a name a module does not export succeeds
silently, failing later at the use site with a misdirected "variable not
found") is mitigated at this lane's base:

- `src/compiler/10.frontend/core/interpreter/module_loader_core.spl:910-950`
  (`warn_unprovided_use_names`): every braced `use` name the resolved module's
  recorded surface does not provide now emits an import-time `[use-warning]`
  naming the module and the name, deduped per (module, name, importer);
  wildcard/opaque surfaces are exempt (no false positives on wildcard
  re-export chains); `SIMPLE_NO_DEPRECATED_WARNINGS` disables it.
- Re-ran this record's repro on the 2026-11-11 seed:
  `use compiler.mir.{MirLowering}` now prints `[use-warning] 'MirLowering' is
  named in `use compiler.mir.{...}` but module '...50.mir/__init__.spl' does
  not provide it` at import time and the program completes (rc=0) — the
  silent, misdirected use-site failure is gone.

Variance from this record's "Expected": the landed parity decision is
WARNING-only ("the module's whole surface stays registered and execution
continues"), not a hard import-time error. The diagnostic-quality harm this
record filed (silent, misdirected) is resolved; the warning-vs-error choice is
the seed-oracle parity decision recorded in the code.

Note: `test/01_unit/bugs/mir_facade_mirlowering_import_spec.spl` fails 1/3 at
tip — its third scenario pins the pre-reorg file `80.driver/pipeline_fn.spl`
(since split into `driver_pipeline*.spl`) and the pre-split import path
(`mir_lowering` -> `mir_lowering_types`). Stale spec pins from the driver
reorganization, not a behavior regression; left as test churn per lane rules.
