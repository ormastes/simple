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
