# LLM Caret GUI Backends — Agent Tasks

- Metal lane: `metal_fix` owns bounded `gui_metal.spl` diagnosis/evidence.
- Verification lane: `independent_verify` owns read-only requirements, tests,
  evidence, documentation, and release-gate review.
- Sync lane: `sync_scope` owns read-only jj scope planning around the concurrent
  WM/theme worktree.
- Implementation owner: current Codex session.
- Merge owner: current Codex session, path-scoped split only.
- Final reviewer: `independent_verify`, followed by the root normal/highest-
  capability Codex acceptance pass.
- Commit scope: Caret source/tests/docs and no WM/theme artifacts.
