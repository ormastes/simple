# Feature Expert: Startup / Launch Ordering

## What this is
The process entry path: how `simple <cmd>` decodes its command and what it is
allowed to initialize before it knows what the user asked for.

**Core rule: decode the command FIRST.** dynSMF and any other dynamic-library
machinery is initialized only by the command branch that actually needs it, so
no-op / `--help` / unknown-option paths pay nothing for it.

## Source of truth
- Plan: `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md`
  §2.1 (the defect), §5.1–5.2 (target design), §3.1 (startup targets),
  §11.3 (phase trace + the no-aspect release gate), §15 P0 list.
- Guide: `doc/07_guide/compiler/startup_ordering.md`

## Code map
| File | Role |
|---|---|
| `src/app/main.spl` | Args decoded first; `dynsmf_startup_session(...)` now created only inside the `--dynsmf-status` branch. |
| `src/app/startup/dynsmf_autoload.spl` | `dynsmf_dispatch_background_compiles` is **no longer called from startup**. Missing artifacts stay QUEUED as evidence. The dispatch fn is kept and exported for explicit callers. Level-gated trace `dynsmf-trace: startup_session_init` under `SIMPLE_DYNSMF_TRACE=1`. |
| `src/os/smf/dynsmf_session.spl` | The seven `default_autoload` entries (file, network, 2D rendering, GUI, web, TUI, HTML UI) are now `false` — demand-loaded. |

Specs: `test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl` (3),
`test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl` (6),
`test/01_unit/os/smf/dynsmf_session_spec.spl`.

The gate spec requires `SIMPLE_BIN` in the environment — without it the child
process fails and the sabotage probe is invalid rather than RED.

## Landmines

- **NEVER benchmark one tree against another.** The implementing agent measured
  "before" in the main repo checkout and "after" in its worktree, and reported a
  **12.4× speedup**. A controlled A/B in ONE tree with ONE binary, toggling only
  the three source files, gave **~13%** (p50 599→521 ms). The 100× discrepancy was
  entirely the tree difference — the shared checkout carries a huge pile of
  uncommitted files and different cache state. Toggle the change, hold everything
  else fixed, and state which tree and which binary produced each number.
- **`--help` timing must be measured via `run src/app/main.spl --help`, not
  `bin/simple --help`.** The deployed binary cannot reflect a `.spl` edit until a
  bootstrap redeploys it, so measuring the binary shows no change and reads as
  "the fix did nothing". Label the number as a source-run measurement.
- **Record binary identity with every timing.** `readlink -f bin/simple` plus
  `stat -c '%s %y'` — other sessions replace that symlink mid-session, and
  `bin/simple` here is currently the Rust **seed**, not the self-hosted binary.
- Startup must not spawn child compilers. Queue the work; do not launch a shell
  and a compiler per missing artifact on the critical path.
- Do not delete probe/trace logging during cleanup — convert it to level-gated,
  default off (`.claude/rules/code-style.md`).

## Verification
```bash
export SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple
bin/simple test test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl   # 3/3
bin/simple test test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl # 6/6
```
Correctness re-runs after any demand-load change: `--dynsmf-status` must still
report artifact status, no-op must print nothing with rc=0, `--help` must print
usage with rc=0. A startup reorder that breaks a command which genuinely needed a
library is a severe regression — name and run a command per demand-loaded
capability.

## Not yet done
- `strace`/openat counts for the no-aspect path were not captured; the §11.3
  release gate ("zero aspect payload maps") is argued by construction, not measured.
- The remaining ~500 ms of `--help` is seed source-run interpretation, not dynSMF.

## 2026-08-18 landed surface (startup-perf campaign)

load_policy axis + wiring (`src/app/startup/load_policy_wiring.spl`) → segment
plans (`segment_load_plan.spl`); dynload SDN/env config (`dynsmf_autoload.spl`)
+ component descriptors (`src/lib/common/structural/component/`); CLI `--x`
registry/config/help/completion (`composition/cli_extension_config.spl`).
Gates: `scripts/check/check-startup-perf-budget.shs`,
`check-coupling-budget.shs`. Lint/parse cost root cause + mitigations:
`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`. Benchmarks:
`doc/10_metrics/startup/cross_language_startup_benchmark_2026-08-18.md`.

## Launch-overhead numbers (measured 2026-08-23, extends the 2026-08-18 doc)

Full table + load context:
`doc/10_metrics/startup/cross_language_startup_benchmark_2026-08-18.md`
§"Re-measurement 2026-08-23". Medians from the one internally-comparable block
(load 46.0/38.6/34.6, 30 runs each, no `hyperfine` on this host):

| lane | median ms | RSS KB | artifact |
|---|---:|---:|---:|
| **Simple native binary** | **9.8** | 1,280 | 22 KB |
| Go native binary | 14.5 | 1,536 | 1.9 MB |
| python3 | 82.6 | 10,496 | — |
| bun | 85.8 | 32,256 | — |
| `simple --version` (process floor) | 89.3 | 14,080 | 60.6 MB |
| `simple run hello.spl` | 143.6 | 27,392 | — |

**A natively-built Simple binary beats Go on startup, RSS and size.** Launch
overhead is not a Simple problem — until 2026-08-23 the lane simply could not be
built (`doc/08_tracking/bug/seed_interpreter_extern_missing_rt_heap_ref_wellformed_2026-08-23.md`).

### Correction: the "82 `src/lib/**.spl` opens on every process start" figure
That number (from `.claude/rules/commands.md`) is about **stdlib edits not
needing a build**, and does **not** describe hello-world startup. Measured:
`strace -c` on `bin/simple run hello.spl` shows **89 openat totalling 1.13 ms**,
of which **5** are `.spl`; one stdlib import makes it 7. File I/O is under 2 ms
of a 76-144 ms run. **Do not cite the 82-open figure as a startup cost.**

The real `run` floor is the **60.6 MB binary** — `--version` compiles nothing and
still costs 30-89 ms, scaling with load (p95 256 ms at load 46). Page-fault +
dynamic-relocation cost, not parsing and not I/O.
