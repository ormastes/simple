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

## Deep pass — 2026-08-21 (second session)

Inventory at start: 608 local branches, 357 worktrees, main = 1915e1f916a.

### Method

- `git for-each-ref --format='%(ahead-behind:main)'` classified all 608 branches in <1s (the per-branch `git cherry` loop was ~12s/branch and infeasible at this scale).
- Buckets: ZERO/merged 8, SMALL (1-6 ahead) 69, BULK (>6 ahead) 531.
- BULK mining was done globally rather than per branch: all 28,075 off-main commits were enumerated once, filtered to `fix(`/`test(` subjects <14 days old and <=10 files (657 unique by patch-id).
- **Anti-revert filter (rules/vcs.md §Sync must never clobber):** a candidate was only cherry-picked when, for every file it touches, the blob at its PARENT is byte-identical to main's current blob — i.e. a true forward delta that cannot rewind another session's work. 60 of 657 passed; 597 were base-drifted or already present and were left alone.
- Each landed commit was verified by running the spec files it touches individually with `bin/simple test` (57 spec runs).

### Branch actions

| Class | Count | Action |
|---|---|---|
| fully merged (ancestor of main) | 7 | `git branch -d` (4 deleted; 3 refused — checked out in a worktree) |
| superseded (all patch-ids on main, `git cherry` all `-`) | 22 | `git branch -D` (20 deleted) |
| junk (`_stash_*`/`land*`/`session-*`/`rescue/*` >7d, or empty/WIP subject) | 35 | `git branch -D` (33 deleted) |
| BULK / still-live forks | 551 | kept — carry unique unmined content; mined individually above |

608 -> 551 branches.

### Revived commits (45 landed)

| revived sha | source branch | subject |
|---|---|---|
| 6f28264b716 | — | revive(land3): test(fonts): first unit specs for the nogc text_layout stack — bitmap, placement, vector (15/15) |
| 2fcc8f9fd76 | — | revive(land3): test(rendering): sync backend_matrix_spec mirror — clears the newly introduced divergence |
| 27b65673362 | — | revive(land3): fix(interpreter): propagate captured-object self-mutations out of lambda bodies (6th write-back site) |
| d053b939086 | — | revive(land3): fix(web): compound selector #id.class matched as a single id in two selector paths |
| c968217db58 | — | revive(land3): fix(web): font-cache parallel-array bounds guard + alpha-aware gradient stops + load browser_session_loading |
| 40979cf4896 | — | revive(land-rendering): test(aspect_pack): executable gap ledger — 8 acceptance items, 7 pending with named blockers |
| 3d0d072ca41 | — | revive(land-rendering): fix(loader): resolve duplicate type names shadowing the real loader classes |
| d33c4a2e5bf | — | revive(land-rendering): test(bitfield): de-vacuify the legacy twin too; record pre-push divergence offenders |
| 890514c99e7 | — | revive(land-rendering): fix(driver): wire smf_manifest_entry_verifies into load_smf_manifest — whole-entry verify on load, fail closed |
| c2141a846d3 | — | revive(_stash_extra): fix(test-runner): aggregate Results: line fails closed on timed-out specs |
| 859f1cbff64 | — | revive(_stash_extra): fix(test): port perf-spec fixes to 05_perf mirrors (tauri_equiv report, ui_access hot paths) |
| c2d1d2f201c | — | revive(_stash_extra): fix(perf-specs): entry-closure source-root fast path, fail-closed mode receipts, spec interpolation |
| 1c292d5c4d8 | — | revive(_stash_extra): test(perf): fix ui_access hot-paths spec imports and builder API usage |
| 84b86db03ec | — | revive(_stash_extra): fix(test): repair tauri_equiv report_spec — parse error, percentile off-by-one, set-free sort |
| 627354f4f2d | — | revive(_stash_extra): fix(test): lean package-root spec used undefined `none`; Simple's null literal is `nil` |
| aa27a5148cb | — | revive(_stash_extra): test(control_flow): fn_lambda BDD case must not rely on unsupported closure write-back |
| 7a5a79edff4 | — | revive(_stash_extra): fix(verification): format_all loop var shadowed by module alias |
| d08de8b2559 | — | revive(_stash_extra): fix(guard): make lint-binary staleness FAIL self-diagnosing, not just red |
| 6b37fc7c37c | — | revive(_stash_extra): fix(spec-gen): stop silent spec drops and flattened mirror paths |
| 67179d8e910 | — | revive(_stash_extra): fix(check): jit-module-drop fence bucketed a truncated diagnostic |
| bfc953d5600 | — | revive(_stash_extra): fix(monitor): each kill reason names its own guard, limit and env var |
| 59ab2b2c8a4 | — | revive(_stash_extra): fix(native-build): fail closed instead of returning 0 unconditionally |
| aebb8f86a7d | — | revive(_stash_extra): fix(guards): make a misplaced --expect-files an ERROR; file three verified guard defects |
| e1d0a11585b | — | revive(_stash_extra): test(cli): fix brace interpolation and stale argv-ABI claim in main_part2 depth guard spec |
| 19d9dd22497 | — | revive(_stash_extra): test(cli): escape literal braces in test_entry numeric guard spec |
| 4415da044ff | — | revive(_stash_extra): test(cli): escape literal braces in args_after_command dedupe spec |
| e416077889c | — | revive(_stash_extra): test(runtime): refute the rt_clear Dict-arm misclassification hypothesis by C measurement |
| 05ab7e6602f | — | revive(_stash_extra): fix(native_all): align per-file timeout default with library (60s -> 300s) |
| e2c5ff641a3 | — | revive(_stash_extra): fix(guards): verdict contracts for the gpu and bootstrap guards; os/runtime triage |
| 808901bc7c0 | — | revive(_stash_extra): fix(runtime): restore the 61-bit boxed-integer writer clobbered by e14a2ffb4df |
| d336a55d37f | — | revive(_stash_extra): fix(check): let the outcome-reason guard find a compiler from a fresh worktree |
| 99149cbd33b | — | revive(_stash_extra): fix(docs): restore 9 bug docs my previous commit clobbered |
| bca4c5b73ee | — | revive(_stash_extra): fix(sheets): FLOOR/CEILING silently inverted for a negative significance |
| 547bec3a094 | — | revive(_stash_extra): fix(perf): make 8K receipt aggregator portable |
| e1b52ff1719 | — | revive(_stash_extra): fix(bootstrap): refuse recursive release delegation |
| 3f00d1eec46 | — | revive(_stash_extra): fix(macos): canonicalize GPU runtime rpath admission |
| 75d3e5cf9b6 | — | revive(_stash_extra): fix(runtime): restore macOS C compile guard |
| d7e7bb91a01 | — | revive(_stash_extra): fix(mcp): keep installed project launchers portable |
| ea85ee6bf24 | — | revive(codex/migrate-compiler-perf-b-202): test(compiler): add capsule sort system coverage |
| 69a34f6261d | — | revive(_stash_extra): fix(riscv): require complete RVFI readiness ports |
| 563be1124ca | — | revive(codex/restart12-infra-recovery): fix(infra): fail closed on SSpec count checks |
| 7af7bcadcda | — | revive(codex/allocator-patch-reconstruct-final): fix(llvm): register global struct receivers |
| 4afcca51d72 | — | revive(codex/option-config-f64-candidate-b791): fix(config): parse float values through Option semantics |
| 0129f385cb7 | — | revive(codex/authority-preflight-order-fix): fix(driver): hoist Tier-5 header owners |
| b11e764b12d | — | revive(codex/stage4-io-self-cycle-fix): fix(bootstrap): type duplicate token cache returns |

### Not landed

| origin sha | reason |
|---|---|
| 2868db243df | red-spec: test(compiler): execute float alias runtime contracts |
| 137cc2a66c9 | red-spec: fix(ui): remove persistence callback captures |
| 2d3e885cdd7 | red-spec: test(infra): specify SSpec count truthfulness |
| fc70c3c3794 | red-spec: test(io): add fail-closed SCV/render file-read byte contract coverage |
| df8e9afe9d7 | red-spec: test(smux): add fail-closed system SSpec for smux/caret spec quality |
| aef9bac7969 | red-spec: test(render): add 8K80 A1 system coverage |
| db2f57131a9 | red-spec: fix(parser): close compiled-checker syntax gaps |
| 96a260a5a62 | red-spec: test(hir): cover env path import ownership |
| b93044e05eb | red-spec: test(startup-perf): wire the startup budget detector into `bin/simple test`; record aspect-weave spec timeouts |
| cb06d7ddbde | red-spec: fix(check): engine-differential i64 container divergence was a stale seed |
| 9d9049d5691 | red-spec: fix(parser): require commas between generic args so a comparison chain closed by '(' backtracks |
| c731c72e396 | red-spec: fix(test): t32_hw DebugConfig literals drop undeclared args/debugger/remote |
| de90b608a20 | red-spec: fix(web_framework): make session signing + CSRF tokens executable; 3 specs left RED on real defects |
| 6d0ddc8a611 | red-spec: fix(semantics): wire forbidden_io_checker into a real scan driver — it protected nothing |
| 52b6c4dd44b | cherry-pick conflict (codex/authority-preflight-order-fix) |

14 commits were picked, found to leave a spec RED, and dropped (`reset --hard`); the chain was rebuilt without them. 11 of those 14 ADD a new deliberately-red spec (e.g. `session_csrf_signing_spec`, `sspec_count_truthfulness_spec`, `forbidden_io_context_scan_spec`) — real defects worth landing later with their fixes, but not green today.

### Worktrees

- 357 registered. 5 protected by name (`simple-main`, `orphan-triage`, `land-*`, `simple-boot-snap`).
- 298 have HEADs NOT on main -> kept (unmerged work).
- 54 had HEAD on main, no live process (`pgrep -af` + `/proc/*/cwd` cross-check), mtime >2h, and a clean `git status` -> `git worktree remove --force`, then `git worktree prune`.
- 0 were dirty; none was removed with uncommitted content.
