# Feature: `simple mem` — interactive memory-profiling CLI (2026-07-29)

## Problem
The infra (per-owner counters, snapshots, arena/GC/GPU stats, RSS sampler)
needs one operator surface. Comparable tools (pprof, heaptrack_gui,
memory_viz) prove the value is in the INTERACTIVE query layer, not raw dumps.

## Proposal
`simple mem <sub>` — Simple-TUI (default UI rule) + plain-text fallback:

- `simple mem top [--pid P | --profile F] [--by-owner|--by-kind|--gpu]` —
  live-refreshing table: live/peak bytes, allocs, per owner/kind/device-pool.
- `simple mem snapshot [--pid P] -o F` / `simple mem diff A B` — capture and
  compare (the leak workflow: diff two snapshots, sort by delta).
- `simple mem trace prog.spl [-- args]` — run with SIMPLE_MEM_ATTR=1 +
  trace record to file; then `top/diff/query` against the file post-mortem.
  Data stays in files; the CLI is the query surface (bytehound model).
- `simple mem gpu [--pid P]` — device pools (reserved/used/high-water),
  NVML/ROCm device truth; `--sanitize` re-execs under compute-sanitizer.
- `simple mem gate` — the CI RSS gate (wraps check-stage4-memory-gate.shs).

Live-process access: existing MCP/daemon plumbing where present, else
signal-triggered dump to a well-known path (`SIMPLE_MEM_DUMP_ON=USR2`).

## Constraints
- Every collector it turns on is config-gated, off by default
  (zero-overhead-when-off HARD RULE, plan cross-cutting req 2).
- Pure Simple implementation (`src/app/memstat` grows into this; keep the
  existing CSV sampler as `simple mem sample`).
- Trace/snapshot format versioned; GPU trace exports
  PyTorch-memory_viz-compatible snapshots.

## Acceptance
`simple mem trace` + `top --profile` on the M1 two-module fixture ranks
owners correctly; `diff` on before/after-leak snapshots surfaces the leak
top-of-list; TUI works in a dumb terminal; all collectors off ⇒ measured
zero overhead.

## Status (2026-07-30)
Verb dispatch COMPLETE (landed ef00d5e2094). Every help-listed verb
dispatches explicitly; unknown verb prints help and exits 1; `top --once`
renders one frame without entering the TUI loop. Spec test
`mem_cli_spec.spl` passes 7/7. Earlier foundation (landed 0917eee9b93d):
SIGUSR2 hook in `signal_handlers.spl`, `mem/dump.spl` v1 TSV snapshot,
spec `mem_dump_spec.spl` 3/3. Remaining work: interactive TUI render,
live-process polling (`top --pid` without MCP), `gpu` subcommand stub
implementation.
