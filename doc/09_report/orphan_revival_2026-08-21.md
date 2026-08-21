# Orphan / off-main work salvage — 2026-08-21

Scope: work stranded off `main` with commit dates within 7 days (>= 2026-08-14).

## Environment facts found during inventory

- **There is no jj repo here.** No `.jj` directory exists at
  `/mnt/data/worktrees/simple-main` or `/home/ormastes/dev/pub/simple`; every
  `jj` invocation returns *"There is no jj repo in ."*. All salvage was done
  with plain git. The `.claude/rules/vcs.md` jj workflow is currently
  inapplicable in this checkout.
- Local `main` has diverged from `origin/main`: **462 ahead / 895 behind**
  (measured at c089809a253). Nothing was pushed.
- The shared working copy is being swept by other live agents. During this
  session a parallel agent's commit (`2470e206322`) absorbed files this session
  had staged — see the parser entry below.
- A **bootstrap is live** (`native-build` pids 1139385 / 1148368) writing
  `bootstrap/.input-snapshot/` (created 05:10 today). That directory is a tree
  of symlinks back into the repo; `.gitignore -> /mnt/.../simple-main/.gitignore`
  is **not** a dangling self-referential link — the "Too many levels of symbolic
  links" warning comes from the snapshot dir living inside the repo it links to.
  **Left untouched: in use by the running bootstrap.**

## Candidate inventory

70 local branches carry commits within the 7-day window. 52 of them are >6
commits ahead of `main` — these are stale rebase bases / whole-session forks
(`land2`, `land3`, `_stash_extra`, `session-2026-08-18-pickup`, the
`codex/migrate-*` and `migrate/restart12-*` families, 869-876 commits ahead in
the worst cases). They are not individual fixes and were **not** treated as
revival candidates; they are recorded here as bulk/junk.

The reviewable set (<= 6 commits ahead):

| Branch | Tip | Date | Ahead | Classification | Reason |
|---|---|---|---|---|---|
| `codex/stage3-optional-continuation-fix` | 9cb28ed7705 | 2026-08-14 | 1 | **(b) revived — landed** | `TOK_DOT_QUESTION` missing from `token_can_end_expr`. Absent from main; merge-tree clean. Spec green 15/15. Landed (see below). |
| `recover/actors-01a00035` | f2643022da5 | 2026-08-16 | 1 | **(b) revived — landed** | `spawn_pool` bypassed the scheduler owner. `spawn_on`/`get_scheduler` both exist on main. Commit `6f1bb1d34e5`. |
| `recover/scv-20260816` | 5fedf74f91e | 2026-08-16 | 1 | **(a) superseded — landed then reverted** | See "Reverted" below. |
| `recover/font-seed-20260816` | 9f6dc690797 | 2026-08-16 | 2 | (b) revivable — **not landed** | Merge-tree clean, but touches the Rust seed (`hir/lower/expr/control.rs`, `stmt_lowering.rs`). Landing untested Rust seed edits risks `check-seed-builds-push.shs`; needs a `cargo check` pass first. |
| `codex/recover-formal-01a00527` | b637ea6f406 | 2026-08-16 | 1 | (b) revivable — **not landed** | 17 files, "recover fail-closed FV2 authority checks". Merge-tree clean but unverified; too broad to land untested in a tree being swept by other agents. |
| `codex/recover-qemu-01a00035` | a1d51cce61e | 2026-08-16 | 1 | (b) revivable — **not landed** | 24 files, QEMU evidence hardening. Same reason. |
| `recover/tiny-20260816` | cab7f102018 | 2026-08-16 | 1 | (b) revivable — **not landed** | 68 purely-additive new files (+5880). Additive, no conflict, but a feature drop, not a fix; needs its own review. |
| `recover/web-20260816` | 761f58b201f | 2026-08-16 | 1 | (c) conflicts | merge-tree CONFLICT on `doc/08_tracking/bug/layout_paint_paint_box_dead_code_*.md`; main moved past it. |
| `codex/render-region-bridge` | 4e695937595 | 2026-08-14 | 1 | (c) conflicts | merge-tree CONFLICT on `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`. |
| `codex/raise-tiny-80-01a00036` | ba6d872f650 | 2026-08-16 | 1 | (c) conflicts | CONFLICT on `doc/00_llm_process/layer_expert/tiny_ui/skill.md`; superseded by `recover/tiny-20260816`. |
| `recover/servers-01a00035` | eb4d0d41c1e | 2026-08-16 | 3 | (c) conflicts | CONFLICT on `test/01_unit/lib/http_server/chunked_rejection_spec.spl`. |
| `secure-servers-01a00035-partial` | 15853895bf5 | 2026-08-16 | 3 | (c) duplicate | Same three commits as `recover/servers-01a00035`, different shas. |
| `codex/simpleos-image-wrapper-01a00035` / `codex/simpleos-payload-linker-01a00035` | 69f7722ed70 | 2026-08-16 | 2 | (a) superseded | `git cherry` reports both commits already equivalent-upstream. |
| `codex/simpleos-scalar-metadata-01a00035` | 2a4d2e8bece | 2026-08-16 | 0 | (a) merged | Fully contained in main. |
| `rescue/restart12-qemu-matrix-20260819` | b215137faaa | 2026-08-19 | 1 | (c) junk/WIP | **Empty commit message**; 26-file WIP snapshot. |
| `rescue/restart12-qemu-matrix-preaudit-20260819` | de3c16b6da5 | 2026-08-16 | 1 | (c) junk/WIP | Empty commit message; 25-file WIP snapshot. |

## Revived commits

| Commit | Subject |
|---|---|
| (swept into `2470e206322`) | `fix(parser): continue after optional presence` (from `9cb28ed7705`) — `TOK_DOT_QUESTION` added to `token_can_end_expr`, regression spec, bug record. Verified green (`parser_leading_operator_continuation_spec.spl`, 15/15) **before** commit; a parallel agent's whole-tree commit absorbed the staged files a moment later, so the fix is on main under their commit rather than a dedicated `revive(...)` commit. Content confirmed present at `src/compiler/10.frontend/core/tokens.spl:579`. |
| `6f1bb1d34e5` | `revive(actors): fix(parallel): route actor pools through scheduler owner (cherry-picked from f2643022da5)` |

### Reverted (do not retry as-is)

`7798adaab93` `revive(scv): fix(io): unify file_read_bytes wrapper signature`,
reverted by `a5f70161ed0`. The branch predates main's current state on two
axes:

1. It reintroduced `val Some(db) = db_opt` **without** an `else:` clause in
   `src/lib/scv/integrity.spl` — main's parser now rejects a refutable `val`
   binding without a diverging `else:`, so the whole stdlib failed to parse.
2. With that repaired, it still regressed
   `test/01_unit/lib/scv/fast_import_byte_text_spec.spl`: the tag payload
   decoded as `?` instead of `ÿ`, i.e. the `[i64]` wrapper it switches to is
   the wrong one for main's byte path.

The *underlying* problem it was aimed at is still real and still visible on
main: every test run prints
`public function file_read_bytes has 2 co-compiled definitions with 2 differing
signatures ((text)->[i64] vs (text)->[u8])`. That needs a fresh fix written
against current main, not this revival.

### Verification note

`recover/actors-01a00035` has no dedicated spec. `test/feature/usage/actors_spec.spl`
is zero-examples (pre-existing) and `test/feature/usage/actor_model_spec.spl`
fails on unrelated Vec3 message assertions (pre-existing, not touched by this
one-line change). The change was verified by symbol existence only:
`spawn_on` (`actor/spawn.spl:166`) and `get_scheduler` (`actor/scheduler.spl:551`).

## Cleanup performed

- **Stale worktree records pruned**: `git worktree prune` removed **87** admin
  entries whose gitdirs no longer exist (443 -> 356 registered worktrees). No
  directory on disk was deleted.
- **Branches deleted** (fully merged into main, `-d`, no `-D` used):
  `codex/cross-lang-perf-failclosed` (e67f4f53c7d),
  `codex/extern-inline-empty-fix` (40e2417de14).

## Deletion candidates left in place — in use

Merged into main and therefore deletable, but each is checked out by a live
worktree, so git refused and no force was applied:

| Branch | Held by worktree |
|---|---|
| `codex-render-perf` | /home/ormastes/dev/pub/simple-render-perf-resume |
| `codex/bytes-evidence-fresh` | /mnt/data/bytes-evidence-fresh |
| `codex/llvm23-binding` | /home/ormastes/dev/pub/simple-llvm23-binding |
| `codex/perf-trace-scheduler-fix` | /mnt/data/worktrees/perf-trace-scheduler-fix |
| `codex/perf-upstream-port-fb21207` | /mnt/data/bs2/perf-upstream-port-fb21207 |
| `codex/post-stage4-perf-gate` | /mnt/data/worktrees/post-stage4-perf-gate |
| `codex/simpleos-scalar-metadata-01a00035` | /mnt/data/worktrees/restart12-simpleos |

Also left in place: `bootstrap/.input-snapshot/` (live bootstrap), and the 356
remaining registered worktrees — no worktree directory was removed, because a
bootstrap and several agent sessions are running against this repo and a
per-directory liveness check across 356 trees was not affordable on a loaded
host. Nothing was pushed; no branch was created.
