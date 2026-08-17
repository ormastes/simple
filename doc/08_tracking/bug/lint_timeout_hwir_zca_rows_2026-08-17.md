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

## 2026-08-17 bounded source fix

No profiler capture exists beyond the wall-clock/log-freeze evidence above,
so the earlier superlinear-per-declaration attribution remains a hypothesis.
Static audit did identify one avoidable deep pass: `check_required_comment`
recursively walks and recopies warning arrays through nested expressions even
when the source contains none of the REQC trigger families. `zca_rows.spl` is
a 132148-byte builder-heavy AST and contains no such trigger.

The lint CLI now uses `required_comment_source_may_match`, a conservative
linear admission check, before that recursive walk. It covers `pass_*`,
`todo(...)`, wildcard cases, and every name in the live dangerous-keyword
registry, including names registered later. The focused regression reads the
exact Zca file and proves rejection while adjacent wildcard and dangerous-name
sources remain admitted.

Status: **SOURCE FIXED / RUNTIME TIMING PENDING**. This isolated worktree has
no deployed pure-Simple CLI with a `lint`/`test` command; the available shared
staged bootstrap executable exposes compile flags only. Per repository policy
no Rust-seed fallback was used, and the 900-second command was not repeated.
A deployed pure-Simple binary must run the focused spec and a bounded lint
timing before this record can close.

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
