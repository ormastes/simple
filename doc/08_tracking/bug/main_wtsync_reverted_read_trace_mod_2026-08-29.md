# main: chore(wtsync) commit reverted `pub mod read_trace;` — repo main unbuildable

**Filed:** 2026-08-29 (found by sort_by v2 Opus verification)
**Status:** OPEN — affects repo `main` tip (4ee2dba580d), NOT release/2026-08-27

A `chore(wtsync)` commit removed `pub mod read_trace;` from
`src/compiler_rust/compiler/src/lib.rs` while leaving `read_trace.rs`
committed — the stale-snapshot sync-clobber class (.claude/rules/vcs.md
"Sync must never clobber"). Baseline and patched worktrees fail with a
byte-identical error set. Fix: restore the mod line on main (one line).
Evidence: $SCRATCHPAD/VERIFY_seed_dispatch_v2.md top-line finding.
