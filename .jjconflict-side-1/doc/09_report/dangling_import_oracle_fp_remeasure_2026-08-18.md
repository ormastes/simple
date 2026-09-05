# Dangling-import detector: replacing the 93%-FP text scanner with a resolution oracle (2026-08-18)

Lane FPCENSUS. Follow-up to `doc/09_report/dangling_import_census_2026-08-18.md`
(commit `b7e87a91507`). Tool under test: `bin/simple`, the **Rust seed** — every
diagnostic quoted here is the seed's, not a self-hosted binary's. `bin/simple`
was NOT rebuilt or redeployed.

## The defect being fixed

The census reported 307 module-level / 444 symbol-level dangling `use` edges and
honestly self-reported a **false-positive rate of ~93% (14 of 15 hand-checked)**.
A detector at 93% FP is worse than no detector: it trains everyone to ignore it.
That, not the edge count, was the defect.

Its author named the two FP generators it could not follow, and both are
legitimate, widespread Simple idioms rather than scanner bugs:

1. `pub use <BareName>` — re-exports a *local* binding, not a module path.
2. plain whole-module `use <module>` — the re-exported symbol universe is
   unknowable to a text scanner.

Neither is fixable with more regex. Both require real name resolution.

## What was done: stop scanning text, ask the compiler

The census's own systemic verdict already contained the answer — *"the seed
already detects this defect class correctly"*. Its `[use-warning]` is a working
symbol-level dangling-import checker and its `Cannot resolve module` a working
module-level one; the only failure is that a dangling *symbol* is a non-fatal
warning on an **rc=0** run, so it accumulates until someone reads the log.

`scripts/check/check-dangling-imports.shs` reads the log. Because the hits come
from the resolver rather than a scanner, **both FP classes above are structurally
impossible**: the resolver follows `pub use <BareName>` and whole-module
re-exports natively.

### Oracle surface — what exists, measured, with the commands tried

| command | result | oracle? |
|---|---|---|
| `bin/simple run <f>` | 3 `[use-warning]` on `src/lib/nogc_sync_mut/platform_measurement_observer.spl` | **yes — the only one** |
| `bin/simple compile <f> -o …` | **0** use-warnings on that same file | no |
| `bin/simple check <f>` | rc=0, 0 use-warnings, style lint only | no |
| `bin/simple symbols` | `error: file not found: symbols` | does not exist |
| `bin/simple ast-query` | `error: file not found: ast-query` | does not exist |

Stated explicitly as the brief requires: **the seed exposes no
`ast-query` / `symbols` / `--emit` resolved-import dump.** `simple_symbols` and
`lsp_symbols` are MCP surfaces over a *self-hosted* binary, which this lane is
forbidden to build. So the oracle is `run`, with a timeout and `</dev/null`,
accepting that `run` executes top-level code.

### Two module-level diagnostic forms, not one

A harvester that knows only one form is fail-open. Measured on the same fixture:

- interpreter/semantic path → ``error: semantic: Cannot resolve module: M``
- JIT/HIR-lowering path → ``cannot resolve import `M`: … code E1034``

The real defect `src/lib/nogc_sync_mut/mcp/jj/helpers.spl` emits the **first**; a
fresh out-of-tree fixture emits the **second**. Both are harvested.

## Ablation (causation, not correlation)

The harvest was first written with `sed "s/…/module\t$f\t\1\t-/p"`. The importer
path contains `/`, which breaks the `s///` delimiter.

| state | `--resolve-one src/lib/nogc_sync_mut/mcp/jj/helpers.spl` | `--selftest` |
|---|---|---|
| ablated (sed, path in RHS) | ``sed: -e expression #1, char 61: unknown option to `s'`` — **0 edges** | `SELFTEST FAIL … produced 0 edges, expected >=1`, exit 2 |
| restored (awk) | `module	…/helpers.spl	app.mcp_jj.jj_runner	-` | `selftest: 2 fixture(s) OK` |

Applied → verified → removed → regression confirmed → restored. Note the failure
mode: the broken harvester reported the **whole tree clean**. The fail-closed
selftest is what caught it, and it is run before every scan.

## Re-measurement — new FP rate

Run: `--sample 800 --seed 20260818 --jobs 8 --timeout 45` over
`src/lib src/app src/compiler src/os` (`find -L`, Owned-Code Scope excluded).

```
FAIL — 800 file(s) resolved (21 unverified: timeout/OOM), 112 dangling edge(s)
```

19 module-level, 93 symbol-level, across 49 distinct importers. 21 files are
reported **UNVERIFIED** (timeout/OOM), never folded into the clean count.

A **fresh random sample of 22 surviving hits** (seed 777, drawn from the 112) was
hand-verified one by one — for each, locating the definition of the named symbol
and the named module on disk:

| category | count | share |
|---|---|---|
| **confirmed-defect** | **16 / 22** | **73%** |
| unresolvable | 6 / 22 | 27% |
| facade-idiom (the old FP classes) | **0 / 22** | **0%** |

**False-positive rate: 0 of 22 proven false positives.** Treating every
`unresolvable` as if it were an FP gives a strict **upper bound of 27% (6/22)** —
against the text scanner's measured **93% (14/15)**. The two facade idioms that
generated ~93% of the old hits produced **zero** hits here, which is the expected
consequence of resolving instead of scanning.

### The 16 confirmed defects

Each names a symbol or module that provably is not provided by the module named
in the `use`:

- `mod_exp` (x2), `WM_EVENT_FOCUS` — defined **nowhere** in owned `src/`.
- `rt_ptrace_single_step`, `rt_dwarf_load`, `rt_ptrace_write_memory` — imported
  from `std.sffi.debug`; that module (`src/lib/nogc_async_mut/sffi/debug.spl`)
  contains **zero** `rt_ptrace` declarations.
- `font_execution_plan_into` (x3) — imported from
  `std.gc_async_mut.text_layout.font_renderer`, actually defined in
  `src/lib/nogc_sync_mut/text_layout/font_types.spl:206`. Wrong module named.
- `ProcessId` — imported from `common.window_protocol.geometry`, defined in
  `src/lib/common/types.spl:13`.
- `CapabilitySet` — imported from `std.fs_driver.capability`, defined in
  `src/os/kernel/types/capability_types.spl:91`.
- `input` — imported from `common.ui.builder`; `src/lib/common/ui/builder.spl`
  does not define or re-export it.
- `app.debug.remote.target.target_info`, `app.ffi_gen.parser`, `intern_codegen`,
  `compiler.treesitter` — module-level. All four are the **same root-scoping
  class as the census's confirmed `app.mcp_jj.*` cluster**: the target file
  exists in the tree but not under the named root. `src/app/ffi_gen/` contains
  only `test_*.spl` — no `parser.spl`, no `intern_codegen.spl`; the real files
  are under `src/compiler/*/sffi_gen/`.

### The 6 unresolvable — reported, not hidden

`g_vfs` (x2), `g_c_adapter` (x3), `g_mount_table`, all imported from
`os.services.vfs.vfs_boot_init`. The resolver names
`src/os/services/vfs/vfs_boot_init.spl` and says it does not provide them — but
that file **visibly defines all three** as top-level `var` at lines 77, 102, 133.

This was ablated rather than assumed. Four minimal fixtures — a primitive `var`,
a class-typed `var` with a constructor initializer, a multi-line brace import,
and a `var` declared before later class declarations — **all resolve cleanly**.
None reproduces the refusal. Running the defining module directly fails for an
unrelated reason (`error: stack overflow: recursion depth 1000 exceeded limit
1000 in function 'new'`), which does not explain a *symbol-table* gap.

So this cluster is **not** claimed as a defect and **not** dismissed as an FP.
It is an unexplained oracle limitation, and it is the honest 27%.

## What was deliberately left

- **The 112 edges were not fixed.** This lane's mandate was the detector's FP
  rate, not the backlog. 112 is a sample-derived figure from 800 of ~13,667
  files and is labelled an **UPPER BOUND** as a tree-wide count, since only 22
  were hand-verified.
- **No full-tree run.** ~800 files took ~11 min at 8-way on a box at load 33
  with ~15 concurrent lanes; the full tree is ~3 hours of shared CPU.
- **The `vfs_boot_init` limitation was not root-caused.** Four ablations failed
  to reproduce it in isolation; it needs the resolver's own tracing.
- **Not wired into any pre-push hook.** It runs the compiler over the tree and is
  far too slow to gate a push; it is a periodic audit, like
  `watch-origin-tree-health.shs`.

## Verdict

| detector | FP rate | how measured |
|---|---|---|
| text scanner (census, `b7e87a91507`) | **~93% (14/15)** | hand-check, seed 11 |
| resolution oracle (this lane) | **0/22 proven FP; <=27% (6/22) upper bound** | hand-check, seed 777, 22 of 112 |
