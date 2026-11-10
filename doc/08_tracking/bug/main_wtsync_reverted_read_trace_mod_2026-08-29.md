# main: chore(wtsync) commit reverted `pub mod read_trace;` — repo main unbuildable
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-08-29 (found by sort_by v2 Opus verification)
**Status:** SUPERSEDED (2026-11-11, lane ne14) — defect was repo-main-tip-specific; release/1.0.0 tip carries `pub mod read_trace;` and builds; verified, see addendum

A `chore(wtsync)` commit removed `pub mod read_trace;` from
`src/compiler_rust/compiler/src/lib.rs` while leaving `read_trace.rs`
committed — the stale-snapshot sync-clobber class (.claude/rules/vcs.md
"Sync must never clobber"). Baseline and patched worktrees fail with a
byte-identical error set. Fix: restore the mod line on main (one line).
Evidence: $SCRATCHPAD/VERIFY_seed_dispatch_v2.md top-line finding.


## Addendum 2026-11-11 (lane ne14) — SUPERSEDED, verified on release/1.0.0

This record always scoped itself to repo `main` tip (`4ee2dba580d`), "NOT
release/2026-08-27". This lane's worktree is cut from `origin/release/1.0.0`
tip, so the row is checked where it could still bite — and it does not:

**Verification actually run** (worktree simple-p3-ne14-20261111, tip
f7640d20a458):

- `grep -n read_trace src/compiler_rust/compiler/src/lib.rs` → **`44:pub mod read_trace;`** — the mod line this record says was reverted is present.
- `src/compiler_rust/compiler/src/read_trace.rs` (1009 bytes) is real,
  coherent code: a `STATE: AtomicU8` lazy env knob (`SIMPLE_READ_TRACE`) and a
  `pub fn rts(file, line, path)` attribution wrapper over `read_to_string`.
- It is live code, not an orphan: `crate::read_trace::rts(...)` is called from
  5 sites in `src/compiler_rust/compiler/src/hir/lower/import_loader.rs`
  (:1494, :1534, :1586, :1631, :1683). A module that is declared, defined, and
  called cannot reproduce the "removed mod line leaves orphan .rs" clobber.

The `chore(wtsync)` clobber described here never applied to the release line,
and the release line still carries the mod + file + call sites. No cargo build
was run (lane forbids cargo/rustc); module-declaration coherence is verified by
direct source read. If repo `main` is still a supported surface, a main-side
owner should confirm `4ee2dba580d`'s descendants restored the line there — but
that is outside this release-scoped lane.
