# Bug: source-mode MCP server stalls mid-workload under load (stdio, seed interpreter)

- **Found:** 2026-08-28, MCP parity lane, while measuring before/after legs
  with `scratchpad/ab/drive2.py` against
  `<seed> run src/app/mcp/main.spl` (seed:
  `/mnt/data/worktrees/goal-bootstrap/bin/release/x86_64-unknown-linux-gnu/simple`,
  shared box, load 20-80).
- **Symptom:** the server answers a prefix of a JSONL request stream, then
  stops responding to the next `tools/call` and sits idle (a few seconds of
  CPU total, state S) until the harness timeout (600-1800 s). Three distinct
  stall points observed in one afternoon, all with per-request handler cost
  independently measured at 1.2-2.5 s:
  1. combined leg: answered ids 1-6, died writing id 7 (drive2 got
     BrokenPipe — process exited);
  2. exec leg (code at 379daefd14d): stalled on the first
     `simple_ctx_execute` (`cat` of a 197,759 B file), twice, 0 responses
     after `initialize`+`notifications/initialized` in one of the runs;
  3. exec leg (patched code): same request answered handler-level in 1.9 s,
     stalled E2E; search leg (patched): answered the batch, stalled on a
     search the handler answers in 1.4 s.
- **What it is NOT:** a property of either code version — both the
  379daefd14d file and the parity-patched file stall in some runs and answer
  in others; the same handlers called directly (`bin/simple run` a probe that
  imports `app.mcp.main_lazy_ctx_tools`) never stalled across ~10 runs.
- **Suspects (unverified):** stdio framing/read loop in
  `nogc_sync_mut.mcp_sdk.transport.stdio` under a slow writer, or
  interpreter-side blocking when a `tools/call` runs a subprocess while the
  parent's stdin has the next request buffered. The [gc-warning]
  higher-layer-import warnings on startup are unrelated noise.
- **Impact:** E2E latency/stability measurements on the source-mode server
  are unreliable on a loaded box; the parity lane's before/after evidence was
  therefore taken handler-level (documented in
  `doc/01_research/app/mcp/context_mode_ponytail_originals_vs_mimic_2026-08-28.md`
  §4.1). The deployed native server may or may not share the defect — it
  predates the ctx tools entirely, so this could not be tested natively.
- **Repro:** `scratchpad/parity/run_leg.sh <label> exec` (drive2.py + the
  request builder `mkreq_parity.py`) on a loaded host; logs
  `scratchpad/parity/leg_before_exec.log`, `leg_after_*.log`.
- **Next:** retry on the natively-built server after the mcp_health redeploy;
  if it reproduces, strace the read loop at the stall point.
