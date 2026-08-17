# `[WARN] Failed to load imported types` is fail-open: type checking proceeds on nothing

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Filed:** 2026-08-07
**Component:** `src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs`
(lines 1246 and 1823 — the only two sites in the repo that emit this string)
**Related:** `doc/08_tracking/bug/undeclared_imported_symbols_census.md` (the
symbol-level half of the same fail-open family)

## 1. The defect

When HIR module lowering cannot resolve an import, it prints

```
[WARN] Failed to load imported types from ["lib", "database", "bug"]: Module resolution error: ...
```

and **continues**. The importing module is then type-checked with the imported
module's types entirely absent. Nothing downstream reports that the check was
vacuous. The build exits on whatever unrelated error comes later, or exits 0.

This is the documented repo anti-pattern: a verification layer that fails open.
An unresolved *name* is already only a warning; an unresolved *module* being only
a warning too means there is no severity level at which a broken import stops the
build on the `native-build` path.

## 2. Evidence — the stage-3 log

Two independent stage-3 `native-build` runs of the pure-Simple compiler
(`/home/ormastes/dev/simple-s3red/build/red/stage3.log` and
`/home/ormastes/dev/simple-s3family/build/green/stage3.log`, both `rc=1`)
emit **exactly 7** of these warnings, identical in both:

| # | module path | shape |
|---|-------------|-------|
| 1 | `["app","build","quality"]` | E1034 `module path segment 'app' not found` |
| 2 | `["lib","database","checker"]` | E1034 `module path segment 'database' not found` |
| 3 | `["lib","database","bug"]` | E1034 |
| 4 | `["lib","database","feature"]` | E1034 |
| 5 | `["lib","database","test"]` | E1034 |
| 6 | `["lib","database","todo"]` | E1034 |
| 7 | `["std","nogc_sync_mut","baremetal","config"]` | Semantic: "resolves from the project stdlib roots only" |

None of the 7 caused the build to fail. `rc=1` came from an unrelated inline-asm
error at the very end of the log:

```
error: <inline asm>:2:25: unexpected token in argument list
        movzx eax, byte ptr [{addr}]
```

Seven imports type-checked against nothing and nothing failed on their account.

## 3. The causal chain is visible in the same log

`src/app/check_dbs/main.spl` imports `lib.database.bug`. That import fails →
its types load as nothing → every symbol it declared is now undeclared → the
calls become the *warning*-level `unresolved call` family that also floods the
same log. Two warning levels in sequence, no error at either.

## 4. All 7 were dead imports, not resolver defects

Checked against `origin/main` content, not the shared working copy:

- **`lib.database.*` (5).** No `src/lib/database`. The module exists in two tiers,
  `src/lib/nogc_sync_mut/database/` and `src/lib/nogc_async_mut/database/`, with
  identical signatures for the four `load_*_database` entry points. Tier eliding
  is real under the `std.` root but **not** under `lib.`: all 12 distinct working
  `use lib.X` imports in the tree map to a literal `src/lib/X`. Fixed in
  `77d234b4fe91cd5836a9c3fd68c356ca96075dd8` by moving to `std.database.*`, which
  is also the dominant idiom already in the tree (17x `std.database.bug`, 16x
  `std.database.feature`).

  Tier note, since "which tier does `std.X` mean" is not obvious from the import:
  `STDLIB_FAMILY_DIRS` in
  `src/compiler_rust/compiler/src/module_resolver/resolution.rs:20` is searched in
  order and lists **`nogc_async_mut` first**, so `std.database.bug` resolves to
  `src/lib/nogc_async_mut/database/bug.spl`. That matches the repo's
  nogc_async-is-the-default-tier convention and matches what the other 17 call
  sites already get. The one `compat_root = nogc_sync_mut` special case at
  `resolution.rs:667` applies only to the single segment `io`.
- **`app.build.quality` (1).** `src/app/build/` on `origin/main` contains only
  `cli_entry.spl`. All six imported symbols — `CheckResult`, `QualityResult`,
  `default_lint_config`, `default_check_config`, `Lint`, `Check` — are declared
  nowhere in the repo. Three live importers depend on it
  (`src/app/check/render_adapter.spl`, `src/app/lint/render_adapter.spl`,
  `src/app/ui.render/core.spl`), and `core.spl` also imports four *other*
  missing `app.build.*` modules (`types`, `config`, `orchestrator`,
  `render_adapter`). Already enumerated in the census doc; not repaired here
  because repairing it means deciding the fate of a whole dead namespace.
- **`std.nogc_sync_mut.baremetal.config` (1).** No `config.spl` in
  `src/lib/nogc_sync_mut/baremetal/`, and `parse_hostcomm_config` was declared
  nowhere. Implemented as a real `key = value` parser over the existing
  `HostCommConfig` in `a63644675e69fb7c43a774ac4e2e60cdf5e36507`. That commit
  states its own evidence limit: the baremetal package cannot be lowered
  end-to-end because `std.nogc_sync_mut.baremetal.factory` (`create_loopback`,
  imported by `host_comm.spl` and `mod.spl`) is *also* missing, so no GREEN
  lowering evidence exists for the parser body.

## 4a. Still open after this pass

| module path | why not repaired here |
|-------------|----------------------|
| `app.build.quality` | three live importers plus four sibling missing `app.build.*` modules; repairing it is a whole-namespace decision, not an import fix |
| `std.nogc_sync_mut.baremetal.factory` | blocks all baremetal lowering; not in the 7 because `mod.spl`/`host_comm.spl` are not reachable from `bootstrap_main.spl` |

## 5. The `src/app/check/app` doubled path is a diagnostic artifact, not a bug

The E1034 help for `app.build.quality` reads

```
help: check that the module exists at ".../src/app/check/app"
```

which looks like a relative base concatenated with an absolute-style path. It is
not. The resolver searches four candidates — cwd, `src/`, `src/lib/`, and the
**importing file's own directory** — and the `native-build` E1034 help prints
only *one* of them, the importer-relative candidate. The same resolver on the
`compile --format=smf` path prints the full list and makes this obvious:

```
unresolved import 'lib.database.checker' (used in src/app/check_dbs/main.spl):
  no source file found for this module path relative to the working directory,
  src/, src/lib/, or 'src/app/check_dbs'
```

The importer is `src/app/check/render_adapter.spl`, so the importer-relative
candidate is `src/app/check/` + `app/build/quality` = `src/app/check/app/...`.
Nothing is doubled; one of four candidates is being reported as if it were the
whole search. **Fixing the message resolves zero imports** — `src/app/build/quality`
does not exist on any candidate path. It is still worth fixing: it sent this
investigation looking for a resolver defect that is not there.

## 6. The same defect class outside the stage-3 build graph

The warning only fires for imports reachable from `bootstrap_main.spl`. A static
sweep of `^use lib.X` over `src/**/*.spl` finds **16 dead imports** of this exact
class; only the 5 `database` ones were in-graph and therefore only those 5 were
ever visible:

| prefix | count | real location | status |
|--------|-------|---------------|--------|
| `lib.database.*` | 5 (`src/app/check_dbs/main.spl`) | `src/lib/nogc_sync_mut/database/` | fixed, `77d234b4fe9` |
| `lib.yaml.*` | 6 (`src/lib/common/yaml/{parse,serialize,utilities,validate}.spl`) | `src/lib/common/yaml/` — **self-imports** | fixed, `f6ef119799a` |
| `lib.parser.*` | 3 (`src/app/interpreter/parser_pure.spl`) | no `src/lib/parser` anywhere | open — genuinely absent |
| `lib.io.vhdl_ffi` | 2 (`src/compiler/70.backend/backend/vhdl/{vhdl_sim_runner,vhdl_simulator}.spl`) | exists in **two** tiers (`gc_async_mut/io/`, `gc_sync_mut/io/`) — tier ambiguous, needs an owner | open |

Six of them were a module importing its own siblings under a prefix that has
never existed. They sat unresolved indefinitely because nothing errors.

Counting note: a first pass over all of `src/` (not just `.spl`) reported 7
additional `lib.torch.*` imports. Those are **prose inside
`src/lib/gc_async_mut/torch/README.md`**, not code — stale documentation, but not
part of this defect. Anchor this sweep to `*.spl`.

## 7. Recommendation

Make the two `module_pass.rs` sites an **error**, not a warning, on the
`native-build` path. The `compile --format=smf` path already treats the same
condition as a hard error (`error: in-process SMF compile: unresolved import
'lib.database.bug'`, exit 1) — the two paths disagree about whether a missing
module is fatal.

Measured caveat, so nobody expects parity: the SMF path is stricter **on the
imports it reaches**, but it short-circuits on the first failing module in a
package and never reaches the rest. It flagged all 5 `lib.database.*` imports in
0.02s; it flagged **0** of the `baremetal.config` one, because
`src/lib/nogc_sync_mut/baremetal/host_comm.spl` fails first on `create_loopback`
(the separately-missing `factory` module) and the package stops there. Deleting
`config.spl` and restoring it produced byte-identical SMF output. So SMF is a
fast oracle, not a complete one, and flipping `native-build` to error is not the
same change as "make it behave like SMF".

Do **not** silence the warning. Blocking work before the flip: the
`app.build.quality` namespace (§4) must be resolved first, or turning the
warning into an error breaks the stage-3 build outright.
