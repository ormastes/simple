## Re-verified 2026-08-17 - STILL OPEN, WORSE than filed

Re-ran `nice -n 19 timeout 900 sh scripts/check/lint-cached.shs
src/compiler/50.mir/hwir/zca_rows.spl`. It exceeded **900s** (not just the 600s
in the original filing) and produced **no verdict line**; the log froze at 382
lines after the module-load `[gc-warning]` block and never advanced. Killed
manually.

Measured file shape (for the cost model): **1901 lines, 30 function decls**.
At the documented ~11.7s startup + ~3.3-4.0s/decl that predicts ~130s, so the
observed >900s is **~7x above** the linear prediction - consistent with the
superlinear per-decl cost being the root cause, and it means the published cost
model under-predicts badly on this file. Profiling the linter on this file
remains the right next step.

# Lint timeout (>600s) on src/compiler/50.mir/hwir/zca_rows.spl

- Date: 2026-08-17
- Command: `sh scripts/check/lint-cached.shs src/compiler/50.mir/hwir/zca_rows.spl`
  (via seed `bin/simple lint`), killed by `timeout 600` (rc=124), no verdict line.
- Context: sequential lint sweep of files changed vs origin/main; sibling files
  (`driver_public_compile_process.spl`, `store.spl`) linted in normal time in the
  same session.
- Known cost model (`.claude/rules/commands.md`): ~11.7s startup + ~3.3-4.0s per
  function decl, superlinear. `zca_rows.spl` appears to exceed the 600s budget on
  its own, so per-decl superlinearity makes this file un-lintable in practice.
- Expected: single-file lint completes within the 600s budget or the linter
  reports partial progress.
- Follow-up: profile lint on this file; the superlinear per-decl cost is the
  suspected root cause.
