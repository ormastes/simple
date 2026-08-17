# Coupling/Cohesion Baseline — startup / CLI / loader / interpreter (2026-08-17)

BEFORE gate for the startup-surface refactor. All numbers measured 2026-08-17 on
`main` working tree.

## Binary identity

- `readlink -f bin/simple` → `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple` (59,537,240 bytes, mtime 2026-08-17 12:58:51 UTC)
- `bin/simple --version | head -2` → self-identifies as the **Rust bootstrap seed** ("this Rust-built Simple binary is a bootstrap seed only").

## Measurement method

1. `bin/simple deps fast <file>` was run for all four roots (<120s each). It reports
   **direct imports + spot cycles only** and reported `Direct imports: 0` for
   `src/app/cli/__init__.spl` (that file genuinely has zero `use` lines — CLI uses
   "all submodules automatically available" + bare `export` lists), so closure
   numbers below come from a static import-graph resolver:
   `python3 <scratchpad>/dep_baseline.py` — parses `^\s*(export\s+)?use <module>`
   per file, resolves against `src/`, `src/lib/` (std.*), `src/app/`,
   `src/compiler/` (with `NN.layer` prefix mapping) and ancestor dirs, then
   computes reachable closure, Tarjan SCCs (cycles), and wildcard re-export hubs
   (`export use X.*`). Script preserved in session scratchpad; logic is fully
   described here so it is reproducible.
2. Fan-in: `/usr/bin/grep -rlE '^\s*(export\s+)?use\s+.*(<pat>)' src --include='*.spl' | wc -l`
3. Wildcard hubs: files in the closure containing `^\s*export\s+use\s+...\.\*`.
4. Cohesion: `find <dir> -name '*.spl' | xargs wc -l | awk '$1>800'`.

## Baseline table

| module | closure (files) | cycles (SCCs>1) | files-in-cycles | largest cycle | fan-in | fan-out (direct) | wildcard hubs in closure | notes |
|---|---|---|---|---|---|---|---|---|
| `src/app/cli/__init__.spl` | 1 | 0 | 0 | 0 | 45 | 0 | 0 | Zero `use` lines by design ("submodules auto-available"); misleading as a root — see CLI-dir row |
| **CLI dir aggregate** (all 81 `.spl` under `src/app/cli/`) | **1298** | **30** | **188** | **62** | 45 (`use app.cli.*` importers) | — | **41** | The real CLI coupling surface: 1298-file union closure, one 62-file SCC spanning `src/app/io/*` ↔ `src/compiler/driver/*` |
| `src/app/startup/host_startup.spl` | 10 | 0 | 0 | 0 | 0 (no `use app.startup`/`startup.host_startup` importers) | 3 | 0 | Cleanest surface; `deps fast` agrees (2 direct imports, no cycles) |
| `src/compiler/99.loader/loader/module_loader.spl` | 557 | 21 | 158 | 62 | 2 | 7 (`deps fast`: 16 direct) | 27 | Same 62-file `app/io` ↔ `compiler/driver` SCC reachable from the loader; wildcard hubs concentrated in `src/app/io/*_ops.spl` and `src/compiler/backend/*` |
| `src/compiler/95.interp/mir_interpreter.spl` | 37 | 3 | 15 | 8 | 3 | 3 | 1 | Cycles: attributes↔type_layout↔hir_definitions (8 files), blocks/__init__ cluster (5), std.log↔nogc_sync_mut/log (2). Wildcard hub: `compiler/blocks/blocks/modes.spl` |

fan-out for the static resolver counts distinct resolved `use` targets of the root file only.

## Coupling smells (refactor targets)

- **62-file SCC** joining `src/app/io/jit_sffi.spl`, `src/app/io/cli_commands.spl`,
  `src/app/io/_CliCompile/compile_targets.spl` with
  `src/compiler/driver/driver_hir_pipeline_*.spl` — app layer and compiler driver
  are one mutual-recursion blob; reachable from both CLI and loader roots.
- **41 wildcard `export use X.*` hubs** reachable from the CLI surface (27 from the
  loader alone), heaviest in `src/app/io/{cli_commands,cli_compile,dir_ops,env_ops,file_ops,sysinfo_ops,time_ops}.spl`
  and `src/compiler/backend/{backend_types,backend/mir_to_llvm,linker/linker_wrapper}.spl`.
- Ubiquitous small cycles from the `module.spl ↔ _Module/part.spl` split pattern
  (`attributes ↔ _Attributes/decl_attrs`, `type_layout ↔ _TypeLayout/layout_core`,
  `smf_reader_memory ↔ _SmfReaderMemory/header_parser`, `log ↔ nogc_sync_mut/log`).

## Cohesion: files >800 lines in the four surface directories

| file | lines |
|---|---|
| `src/compiler/95.interp/mir_interpreter.spl` | 1017 |
| `src/compiler/99.loader/loader/module_loader.spl` | 929 |
| `src/compiler/99.loader/loader/compiler_sffi.spl` | 914 |
| `src/compiler/99.loader/module_resolver/resolution.spl` | 814 |

`src/app/cli/` and `src/app/startup/` have no file over 800 lines.

## Repeatable commands (verbatim)

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
bin/simple --version 2>&1 | head -2
timeout 120 bin/simple deps fast src/app/cli/__init__.spl
timeout 120 bin/simple deps fast src/app/startup/host_startup.spl
timeout 120 bin/simple deps fast src/compiler/99.loader/loader/module_loader.spl
timeout 120 bin/simple deps fast src/compiler/95.interp/mir_interpreter.spl
/usr/bin/grep -rlE '^\s*(export\s+)?use\s+.*(app.cli)' src --include='*.spl' | wc -l          # fan-in CLI = 45
/usr/bin/grep -rlE '^\s*(export\s+)?use\s+.*(loader.module_loader)' src --include='*.spl' | wc -l  # = 2
/usr/bin/grep -rlE '^\s*(export\s+)?use\s+.*(mir_interpreter)' src --include='*.spl' | wc -l       # = 3
for d in src/app/cli src/app/startup src/compiler/99.loader src/compiler/95.interp; do
  find $d -name '*.spl' | xargs wc -l | awk '$1>800 && $2!="total"{print $1, $2}'; done
```

Caveat: static-resolver closure numbers are an upper-bound approximation (unresolvable
module paths are dropped; `NN.layer` mapping is heuristic). `deps fast` under-reports
(direct-only, and 0 for the CLI init). For the AFTER gate, rerun the same script with
identical resolution rules and diff row-by-row.
