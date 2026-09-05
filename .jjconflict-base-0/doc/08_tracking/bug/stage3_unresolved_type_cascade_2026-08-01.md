# Stage-3 self-host: 3,890 "unresolved type/name" cascade — ROOT CAUSE

Date: 2026-08-01
Status: root-caused + minimal repro proven; fix candidate NOT yet verified at
full-tree scale (see "Status of the unblock")
Blocks: bootstrap redeploy (#18), L7 Stage-4 verification (#10)

## Verdict (one sentence)

Stage 3 invokes `native-build` **without the `--source src/compiler --source
src/app --source src/lib` roots that Stage 2 passes**; the pure-Simple module
loader then populates `module_surfaces` from the transitive `use` closure only,
so **directory-package sibling files that nothing explicitly imports are never
loaded**, and `resolve_package_sibling_symbols` has nothing to register — every
bare cross-file reference inside a package dies as "unresolved type/name".

This is ONE mechanism, not 331 import bugs.

## Evidence chain

### 1. Stage 2 vs Stage 3 are different CODE PATHS, not just different binaries

From `build/bootstrap/stage3/x86_64-unknown-linux-gnu/{stage2,stage3}-command.transcript`:

| | Stage 2 | Stage 3 |
|---|---|---|
| binary | `stage2-runtime-authority/simple` (seed) | `stage2-admitted/simple` (bootstrap, 2 hits on the identity probe) |
| env | `SIMPLE_NATIVE_BUILD_RUST=1` | (absent) |
| entry | `--entry src/app/cli/bootstrap_main.spl` | bare positional |
| **roots** | **`--source src/compiler --source src/app --source src/lib`** | **none** |
| closure | `--entry-closure` | (absent) |

Script sites: `scripts/bootstrap/bootstrap-from-scratch.sh:1270-1273` (stage 2,
has the roots) vs `:1366-1375` (stage 3, has none). The `--source` omission is
the load-bearing difference; the bare positional is deliberate (with `--entry`
the run delegates to the Rust runtime and would not be self-host evidence).

### 2. Minimal repro — 3 files, no compiler code

```
build/s3repro/pkg2/one.spl   struct Thing:\n    x: i64
build/s3repro/pkg2/two.spl   fn g(t: Thing) -> i64:\n    t.x     # NO import — directory-package
build/s3repro/c1.spl         use build.s3repro.pkg2.two.{g}
```

Run through `stage2-admitted/simple native-build` with the exact stage-3 env:

| run | change | result |
|---|---|---|
| `c1` | as above | **2 × `unresolved type: Thing` in two.spl** |
| `c2` | entry also does `use ...pkg2.one.{Thing}` | 0 unresolved |
| `c1s` | c1 source unchanged, **`--source build/s3repro/pkg2` added** | **0 unresolved, exit 0** |

`c1s` is the only run in this whole investigation that exited 0. Single-variable
change; the flag is the cause.

### 3. The code

`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1031-1067`
`resolve_package_sibling_symbols` — implements directory-package semantics by
iterating **`self.module_surfaces.index_by_name.keys()`** (line 1057) and
registering direct siblings. Its own docstring names the hazard:

> "The seed's flat global registry gives this for free; the entry-closure HIR
> path must register each sibling module's public symbols explicitly, or every
> bare cross-file call in a package dies with 'unresolved name'."

It can only register what is already in `module_surfaces`. `--source <dir>`
is what puts un-imported siblings there. Without it the loop is a no-op for
exactly the files that need it.

### 4. Scale check — the shape matches

3,890 errors / 185 distinct symbols / 326 distinct blamed files. Of the 1,306
distinct (blamed-file, symbol) pairs, **1,029 (79%) name a symbol the blamed
file never mentions textually** — e.g. `src/compiler/70.backend/backend/backend_api.spl`
is blamed for `SymbolId` and contains zero occurrences of it; so is
`src/compiler/50.mir/mir_instructions.spl`, which is a pure `export use` facade.
Error attribution follows the re-export/facade chain, so the per-file grouping
in the log is an artifact — the file list is not 326 independent bugs.

## Second, independent (smaller) defect found

`declare_module_symbols` (`module_lowering.spl:1672-1723`) pre-registers the
module's own **classes, structs, enums, bitfields, traits, functions, consts,
methods** — but has **no `module.type_aliases` loop**. The import path handles
aliases (`module_lowering.spl:580-581`, `SymbolKind.TypeAlias`), so the omission
is local-declaration-only.

Repro `build/s3repro/a1.spl` (7 lines, self-contained):

```
type MyAlias = i64
struct Holder:
    v: MyAlias
fn use_it(h: Holder) -> MyAlias:
    h.v
fn main():
    print("a1")
```

→ 4 × `unresolved type: MyAlias`. Rust-seed control (`SIMPLE_EXECUTION_MODE=interpreter
bin/simple run`) exits 0 and prints `a1`, so it is a pure-Simple-compiler defect,
not a language limitation. Cross-module alias import (`a2.spl`) is fine.

Accounts for **295 / 3,890 (7.6%)** of stage-3 errors — symbols `Symbol` (283,
`type Symbol = HirSymbol` at `src/compiler/20.hir/hir_types.spl:95`),
`HirTypeBindings` (8), `ValueCaptureMap` (2), `SymbolNameMap` (2). Real bug,
fix it, but it is not the stage-3 blocker.

## Corrections to the reported measurements

- **`usize` is NOT a "near-builtin failing to resolve" tell.** All 66 hits are in
  two near-duplicate copies of one file — `src/lib/common/binary_io.spl` and
  `src/lib/nogc_async_mut/binary_io.spl` (24,191 / 24,169 bytes) — which annotate
  fields and params `usize` (e.g. `position: usize` at line 79). Localized, 1.7%
  of errors, unrelated to the cascade.
- **`SymbolId` is not declared "as BOTH `struct` and `class`".** There is no
  `class SymbolId` anywhere in `src/`. Four files declare `struct SymbolId`
  (`src/compiler/20.hir/hir_types.spl:71`, `src/app/interpreter/core/symbol.spl:19`,
  `src/lib/{nogc_sync_mut,nogc_async_mut}/dependency_tracker/visibility.spl:33`).
  The duplicate-declaration / `SymbolTable.define` last-write-wins lead did not
  pan out.
- **`src/compiler/backend` and `src/compiler/70.backend` are the same directory**
  (`backend -> 70.backend` symlink; same for `src/std -> lib`). Both spellings
  appear in the log, but after normalizing, **zero** files fail under both — no
  double-loading. Red herring.
- **"Stage 2 works, so the defect is in the stage2-produced compiler"** is only
  half right. Stage 2 ran with `SIMPLE_NATIVE_BUILD_RUST=1`; it never exercised
  the pure-Simple in-process native-build at all. The right framing is: stage 3
  is the first run of the pure-Simple loader, *and* the first run without
  `--source` roots.
- **"331 distinct .spl files"** — 326 distinct paths, and 79% of the blame is
  misattributed to facade/re-export modules (see §4).

## Fixability

**Pure Simple / shell only. Small.**

Primary fix (1 line of shell, no compiler change): insert
`--source src/compiler --source src/app --source src/lib \` immediately before
`--threads "${selfhost_jobs}" \` at
`scripts/bootstrap/bootstrap-from-scratch.sh:1371`, matching stage 2. Keep the
bare positional entry at line 1376 — do **not** add `--entry` (that reroutes to
the Rust runtime and would void the self-host evidence).

The script has six `--source src/compiler --source src/app --source src/lib`
sites (lines 612, 1220, 1272, 1522, 1695, 1732); the stage-3 invocation is the
only native-build call that lacks them, and history shows it never had them —
this is a long-standing asymmetry, not a regression. There is no comment at the
site justifying the omission; the only nearby note is "Stage3 is optional — the
stage2 binary may lack features needed for pure in-process self-hosting", which
has been masking a missing flag.

Secondary fix (pure Simple, ~8 lines): add a `module.type_aliases` loop to
`declare_module_symbols` at `module_lowering.spl:~1723`, mirroring the struct
loop and defining `SymbolKind.TypeAlias`.

Optional hardening (larger, not required to unblock): make the pure-Simple
module loader enumerate directory-package siblings of every loaded module so
directory-package semantics no longer depend on a caller-supplied `--source`
flag. This is the real asymmetry with the seed's flat global registry.

## Status of the unblock

The **mechanism** is settled and proven at micro scale (`c1`/`c2`/`c1s`). The
**full-tree fix is NOT yet verified** — read this section carefully before
acting.

A full stage-3 `native-build` with the three `--source` roots added was run
(8 threads, exact stage-3 env, `stage2-admitted/simple`). It **did not
complete**: it was terminated at ~02:40 elapsed while still in the
single-threaded parse/load phase, having reached **32 GB RSS**
(`/tmp/kill_simple_monitor.log`, `2026-08-01T23:59:19 WARN pid=677178
rss=32035MB`, argv shows the three `--source` flags). It produced **zero** log
output — stdout was block-buffered and lost on the signal, so there is no
partial evidence either way.

Two things to note about that termination:
- It was **not** the `kill_simple_monitor` daemon. That daemon logged only a
  WARN for this pid (`WARN_MEM_MB=32000`); the log's last `KILL` line is from
  16:28, hours earlier. The CPU/age guard (`MIN_AGE_SECS=60`) did not fire
  either.
- The host was not out of memory (125 GB total, 23 GB free, 93 GB cache).

**Open question that gates the fix:** loading all of `src/compiler` +
`src/app` + `src/lib` through the pure-Simple in-process loader costs >32 GB
before lowering even starts. Stage 2 passes the same roots but runs under
`SIMPLE_NATIVE_BUILD_RUST=1`, so its memory profile says nothing about this.
The `--source` fix may therefore trade an unresolved-symbol cascade for a
memory blowup. Re-run needs: a memory-tolerant environment, line-buffered or
`stdbuf`-forced output, and `KILL_SIMPLE_MEM_MB` raised for the daemon.

If the memory cost proves prohibitive, the correct fix moves to the compiler
(the "optional hardening" above): have the pure-Simple loader enumerate
directory-package siblings of each loaded module on demand, which loads a small
superset of the closure rather than the entire tree.

Until a full stage-3 run is green, **stage 3 stays blocked** and `bin/simple`
must not be redeployed. The script's fail-closed refusal to deploy was correct
behaviour and left `bin/simple` untouched (it is currently the Rust seed —
identity probe returns 0).

## Reproduction assets

All under `build/s3repro/` (untracked scratch, not for git):
`pkg2/one.spl`, `pkg2/two.spl`, `c1.spl`, `c2.spl`, `c1s.spl` (sibling repro);
`a1.spl`, `a2.spl` (type-alias repro); `r2.spl`, `r3.spl`, `repro_glob.spl`
(compiler-tree ladder).
