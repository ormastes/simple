# Phase 8 Ship Plan: DBFS Integration

**Feature:** dbfs-integration
**Phase:** 8-ship (Release Mgr)
**Date:** 2026-04-28
**Branch policy:** work directly on `main` (per CLAUDE.md + `feedback_no_branches`)
**VCS:** jj-colocated git; project-authoritative push wrapper is `sj` (per CLAUDE.md)
**Source-of-truth:** `.sstack/dbfs-integration/state.md` (10 ACs), `verify_plan.md` (Phase 7 sign-off), `refactor_targets.md` (Phase 6 work list), `doc/04_architecture/dbfs_architecture.md` (D1–D12, 13 risks)

This plan is mechanically executable. A Phase 8 release-manager runs sections 1→8 in order; total wall-clock target is ~5 minutes given Phase 7 reports green.

---

## 1. Pre-Ship Gate Checklist

Phase 8 MUST NOT START unless every line below evaluates to PASS. The gate maps directly onto the AC checkboxes in `state.md > Phase Outputs > 5-implement > AC Checkbox Status` and the Phase 7 sign-off in `verify_plan.md §7`.

### 1.1 AC gate (10 ACs)

| AC | Required state | Notes |
|----|----------------|-------|
| AC-1 (engine survey) | `[x]` in state.md | DOC-AC: research-phase deliverable. Currently `[ ]` because the checkbox flips only on Phase 7 sign-off. **Phase 7 (not Phase 8) is responsible for flipping it** — Phase 8 verifies it is `[x]` and does NOT flip the box itself. |
| AC-2 (FsDriver seam) | `[x]` | Already `[x]` in 5-implement. Phase 7 re-verifies. |
| AC-3 (engine usable hosted) | `[x]` | Pager/btree/wal/checkpoint/intent_log all green. |
| AC-4 (NVFS BlobBackend) | `[x]` OR explicit deferral FR filed | **Currently `[ ]` — `arena_as_blob_backend_spec` blocked on missing `std.storage.nvfs_arena`.** See §1.4 below. |
| AC-5 (crash-safe) | `[x]` | WAL/checkpoint/recovery + power-cut harness green. |
| AC-6 (HW direct access) | `[x]` | `dbfs_hw_passthrough_spec` green. |
| AC-7 (FAT32 + boot) | `[x]` | `fat32_no_regression_spec` 6/7; the 1 known compiler path-expression bug must have a tracked bug doc. |
| AC-8 (POSIX shim) | `[x]` | `dbfs_posix_shim_spec` green. |
| AC-9 (test + bench) | `[x]` | All 18 specs green; bench-harness smoke green; the 4 `*_bench.spl` workload files exist (flat layout under `test/dbfs/` is acceptable per Phase 7 §3.3). |
| AC-10 (doc + migration) | `[x]` OR explicit deferral FR filed | **Currently `[ ]` — migration plan section pending.** See §1.4 below. |

### 1.2 Phase 7 §7 sign-off boxes

All eight boxes in `verify_plan.md §7` must be ticked in `state.md > Phase Outputs > 7-verify`:

- §0 preamble: 0 compile-mode hits, spec count matches
- §1 AC-1 through AC-10: each AC has positive command output + negative test result captured
- §2 power-cut: F1–F8 outcomes recorded
- §3 bench: comparison matrix filled with measured ratios; pass criteria evaluated
- §4 non-regression: every grep run, counts captured, FAT32/NVFS/RamFS specs still green
- §5 silent-green: every pattern grepped; zero unjustified hits
- §6 risk-to-evidence: each of R1–R13 has one concrete evidence line
- Phase-5 prerequisite flags (intent_log + checkpoint_ring persistence) **cleared**, not trusted

### 1.3 Phase 5 prerequisite re-verify (don't trust upstream)

Phase 8 re-runs these one-liners cold to confirm Phase 5/6/7 didn't drift:

```bash
# Intent log persists durably (R1)
grep -nE 'arena_append.*DB_WAL|wal_handle' \
  /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/db/dbfs_engine/intent_log.spl
# Checkpoint ring persists durably (R2)
grep -nE 'arena_append.*META_DURABLE' \
  /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint_ring.spl
# spostgre coupling absent (R8)
grep -Rn 'use .*spostgre' \
  /home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/db/dbfs_engine/
# expected: ZERO matches
```

If any of the above changes outcome from Phase 7's recorded result, ABORT ship and route back to Phase 7.

### 1.4 Hard-blocker decision tree (AC-4 / AC-10)

**AC-4 (`arena_as_blob_backend_spec` blocked):** Two options, choose ONE before ship:

- **Option A (preferred if feasible in Phase 7 window):** Land `std.storage.nvfs_arena` path; spec turns green; AC-4 flips to `[x]`. No FR needed.
- **Option B (deferred):** File a Feature Request bug doc `doc/08_tracking/bug/fr_dbfs_nvfs_blob_backend_<date>.md` with the missing import path, the spec file, and the unblock criteria. AC-4 stays `[ ]` but the FR doc is committed in this ship batch and `state.md` is updated to "deferred to <FR-id>". Document the user-visible impact: DBFS works on raw block devices but not yet over NVFS arenas.

**AC-10 (migration plan pending):** Same treatment — either land the migration plan as a doc commit in batch 4 of this ship (preferred), or file `fr_dbfs_migration_plan_<date>.md`.

**Decision must be recorded** in `state.md > Phase Outputs > 8-ship` BEFORE the push command runs.

---

## 2. Commit Batch Order

Phase 5 is **expected** to have committed engine/driver/spec/doc batches by ship time (a separate Sonnet agent is finalizing Phase 5 in batches as this plan is being written). Phase 6 and Phase 7 are expected to add focused commits per their own plans. Phase 8 verifies the chain is present (per §1 gate), then ships them in dependency order. **Push order matters** because each batch builds on the previous batch's tree — never push out-of-order. If §1.3 spot-checks reveal a missing batch, ABORT and route back; Phase 8 does not author the missing batch itself.

| # | Source | Type | Files | Expected commit msg prefix | Status check |
|---|--------|------|-------|----------------------------|--------------|
| 1 | Phase 5 batch 1 | feat | `src/lib/nogc_sync_mut/db/dbfs_engine/**` | `feat(dbfs): embedded engine — pager/btree/wal/checkpoint/intent-log` | `git log --oneline | grep -E 'dbfs.*engine'` |
| 2 | Phase 5 batch 2 | feat | `src/lib/nogc_sync_mut/db/dbfs_driver/**` + `src/lib/nogc_sync_mut/fs_driver/{instance,mount_table,__init__,dbfs_stub}.spl` + `src/os/services/vfs/vfs_init.spl` | `feat(fs): DBFS driver at FsDriver seam, /data mount` | one commit |
| 3 | Phase 5 batch 3 | test | `test/dbfs/**` (specs + bench-smoke + power-cut harness) | `test(dbfs): 18 specs + bench harness + power-cut F1–F8` | one commit |
| 4 | Phase 5 batch 4 | docs | `doc/04_architecture/dbfs_architecture.md` + `.sstack/dbfs-integration/state.md` (research/arch/spec phases) | `docs(dbfs): architecture (D1–D12) + sstack state` | one commit |
| 5 | **Phase 6 refactor** | refactor | items 1–5 in `refactor_targets.md §7` (the 30-min pass): `_resolve_fd`/`_resolve_path` extraction in `dbfs_driver.spl`, dead-import cleanup in `intent_log.spl`, header docstrings in `dbfs_engine/__init__.spl` and `ns_btree.spl`, single-key linear-scan helper in `schema.spl` | `refactor(dbfs): extract handle/path resolution + schema linear-scan helper` | one commit; net **−85 to −115 LoC** |
| 6 | **Phase 7 bench results** | docs | `doc/06_spec/dbfs/bench_results_<date>.md` (or wherever the verify plan §3 puts the comparison-matrix output) + `state.md > 7-verify` updates | `docs(dbfs): Phase 7 bench results + verify sign-off` | one commit |
| 7 | (conditional) AC-10 migration | docs | `doc/04_architecture/dbfs_architecture.md` migration-plan section, OR FR doc per §1.4 | `docs(dbfs): migration plan` OR `docs(bug): fr_dbfs_migration_plan` | conditional commit |
| 8 | (conditional) AC-4 deferral | docs | FR doc per §1.4 | `docs(bug): fr_dbfs_nvfs_blob_backend` | conditional commit |
| 9 | Phase 8 sstack state | docs | `.sstack/dbfs-integration/state.md` (8-ship section + final AC checkbox flips) | `docs(sstack): dbfs-integration phase 8 ship recorded` | one commit |

Total expected: **6–9 commits** depending on conditional batches. **Each commit ≤ 5 files** per `feedback_force_push_kernel_arc` to survive parallel force-pushes.

Verify the chain BEFORE push:

```bash
cd /home/ormastes/dev/pub/simple
git log origin/main..@ --oneline | wc -l   # expected: 6–9
git log origin/main..@ --name-only | grep -cE '^(src|test|doc|\.sstack)/' # expected: matches files-touched count
```

---

## 3. Externs Bootstrap-Rebuild Pre-Check

Per `feedback_extern_bootstrap_rebuild`, after any new `rt_*` extern is added, the bootstrap MUST run before push. State.md already declares "No New rt_* Externs Added" but Phase 8 verifies this independently (belt-and-suspenders).

### 3.1 Detection command

```bash
cd /home/ormastes/dev/pub/simple
NEW_EXTERNS=$(grep -REn 'extern[[:space:]]+fn[[:space:]]+rt_' \
  src/lib/nogc_sync_mut/db/ \
  test/dbfs/ \
  2>/dev/null)
echo "$NEW_EXTERNS"
echo "---"
echo "Count: $(echo -n "$NEW_EXTERNS" | grep -cE '^[^[:space:]]')"
```

**Expected output:** zero matches (count = 0).

### 3.2 Bootstrap command (gated)

If, and ONLY if, the count is non-zero:

```bash
cd /home/ormastes/dev/pub/simple
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

NOT `bin/simple build bootstrap` — that command falls through the wrapper whitelist and silently no-ops (per `feedback_extern_bootstrap_rebuild`).

After the bootstrap completes, re-run `bin/simple test test/dbfs/` to confirm the new compiler still passes the suite. If a regression appears here, ABORT ship.

---

## 4. Push Strategy

### 4.1 Primary path

Per CLAUDE.md (project-authoritative tie-break vs. sync-skill `jj`):

```bash
cd /home/ormastes/dev/pub/simple
sj bookmark set main -r @- && sj git push --bookmark main
```

`@-` is the parent of the current working-copy commit (i.e. the latest committed change). Move the `main` bookmark to it, then push.

**Confirmed constraints (project rules):**
- Work directly on `main`. NEVER create branches (per `feedback_no_branches` and CLAUDE.md).
- NEVER force-push to main (per CLAUDE.md). Rollback is `git revert`, not force.
- NEVER skip hooks (no `--no-verify`, no `--no-gpg-sign`).

### 4.2 Worktree cherry-pick fallback

If `.git/index.lock` is held by parallel claudes (per `feedback_push_via_worktree`):

```bash
cd /home/ormastes/dev/pub/simple
WORK=$(mktemp -d)
git worktree add --detach "$WORK" origin/main
cd "$WORK"
# cherry-pick our 6–9 commits in order
for SHA in $(cd /home/ormastes/dev/pub/simple && git log origin/main..@ --reverse --pretty=%H); do
  git cherry-pick "$SHA"
done
# Pin and push
TIP=$(git rev-parse HEAD)
git update-ref refs/heads/main "$TIP"
git push origin main
cd /home/ormastes/dev/pub/simple
git worktree remove "$WORK"
```

This bypasses jj's `.git/index.lock` and avoids `jj describe` colliding with parallel /dev tracks.

### 4.3 File-count guard (per `feedback_destructive_upstream_detection`)

Wrap the push in before/after counts. **Compare like-for-like** — both sides must use `git ls-tree` (committed-tree count). `git ls-files` would inflate BEFORE with staged-but-forbid-listed dirty-tree files (bin/*.cmd, scilib docs, etc.) and trigger a false ABORT.

```bash
cd /home/ormastes/dev/pub/simple
# Snapshot the local committed tree we are about to push (HEAD = our latest committed change)
BEFORE=$(git ls-tree -r --name-only HEAD | wc -l | tr -d ' ')
echo "File count in local HEAD tree: $BEFORE"

# ... push command from §4.1 or §4.2 ...

git fetch origin
AFTER=$(git ls-tree -r --name-only origin/main | wc -l | tr -d ' ')
echo "File count on origin/main after push: $AFTER"
# After a successful push, AFTER should equal BEFORE (we pushed exactly HEAD).
# A drop indicates destructive upstream rebase; an inflation indicates an unexpected merge.
if [ "$AFTER" -lt "$BEFORE" ]; then
  echo "ABORT: file count dropped ($BEFORE -> $AFTER). See §7 rollback."
  exit 1
fi
```

DBFS adds ~13 driver/engine files + ~20 test files + 1 arch doc. Expected committed-tree delta vs. pre-Phase-5 origin/main is roughly +35 files; an unexpected DROP is a strong signal of a destructive upstream rebase and triggers §7.

---

## 5. WIP-Snapshot Defense (Allowlist + Forbid-List)

Per `feedback_wip_snapshot_half_ship`: the local worktree carries a pre-existing dirty tree from before Phase 5 (and a recent `chore: checkpoint local changes before sync` commit `be7e5091ae` is itself an example of the pattern). Phase 8 MUST NOT ship those files.

### 5.1 Triage command

```bash
cd /home/ormastes/dev/pub/simple
git diff origin/main --stat | head -200
git diff origin/main --name-only > /tmp/dbfs_ship_diff_files.txt
wc -l /tmp/dbfs_ship_diff_files.txt
```

Then split into allowlist-matches and forbid-list-matches:

```bash
ALLOW='^(src/lib/nogc_sync_mut/db/|test/dbfs/|src/lib/nogc_sync_mut/fs_driver/(instance|mount_table|__init__|dbfs_stub|capability)\.spl$|src/os/services/vfs/vfs_init\.spl$|doc/04_architecture/dbfs_architecture\.md$|\.sstack/dbfs-integration/|doc/06_spec/dbfs/|doc/08_tracking/bug/fr_dbfs_)'
grep -E "$ALLOW" /tmp/dbfs_ship_diff_files.txt > /tmp/dbfs_ship_allow.txt
grep -vE "$ALLOW" /tmp/dbfs_ship_diff_files.txt > /tmp/dbfs_ship_forbid.txt
echo "Allowlist count: $(wc -l < /tmp/dbfs_ship_allow.txt)"
echo "Forbid count:    $(wc -l < /tmp/dbfs_ship_forbid.txt)"
```

**Expected:** allowlist ~35–45 files; forbid ~30–60 files (the pre-existing dirty tree).

The 6–9 commits in §2 must touch ONLY allowlist files. Verify per-commit:

```bash
for SHA in $(git log origin/main..@ --reverse --pretty=%H); do
  echo "=== $SHA ==="
  git show --name-only --pretty='' "$SHA" | grep -vE "$ALLOW" || echo "  (clean — only allowlist files)"
done
```

If any commit shows non-allowlist files, ABORT and route back to the upstream phase to rewrite that commit.

### 5.2 Files OK to ship (allowlist — enumerated)

- `src/lib/nogc_sync_mut/db/**` — entire DBFS driver + engine subtree (~13 files)
- `test/dbfs/**` — entire DBFS test subtree (~20 files: 18 specs + bench_harness + power_cut_harness; flat layout is OK per `verify_plan.md §3.3`)
- `src/lib/nogc_sync_mut/fs_driver/instance.spl` — `DbFs(driver: DbFsDriver)` variant + match arms (already verified present)
- `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` — exhaustive-match arms for `DbFs`
- `src/lib/nogc_sync_mut/fs_driver/__init__.spl` — `DbFsDriver` export
- `src/lib/nogc_sync_mut/fs_driver/dbfs_stub.spl` — NEW; `DbFsDriver` struct (FsDriver impl)
- `src/lib/nogc_sync_mut/fs_driver/capability.spl` — IF a `Txn` variant was added (see Phase 4 prereq)
- `src/os/services/vfs/vfs_init.spl` — `/data` DBFS mount addition (root remains FAT32)
- `doc/04_architecture/dbfs_architecture.md` — D1–D12 + (Phase 8) migration plan
- `doc/06_spec/dbfs/bench_results_<date>.md` — Phase 7 bench output (path may vary; allowlist matches `doc/06_spec/dbfs/`)
- `doc/08_tracking/bug/fr_dbfs_*.md` — conditional FR docs per §1.4
- `.sstack/dbfs-integration/**` — sstack state + plan files

### 5.3 Files NOT to ship (forbid-list — enumerated)

These come from the pre-existing dirty tree and parallel agent flows. They MUST NOT appear in any commit shipped by this Phase 8.

- `bin/codex_chrome_devtools_mcp.cmd`, `bin/codex_stitch_mcp.cmd`, `bin/simple_lsp_mcp_server.cmd`, `bin/simple_mcp_server.cmd`, `bin/t32_lsp_mcp_server.cmd`, `bin/t32_mcp_server.cmd`
- `scripts/setup.cmd`
- `doc/01_research/scilib_fortran_port/02_python_api_surface.md`
- `doc/03_plan/agent_tasks/scilib_port_*.md` (all `scilib_port_*` task docs)
- `doc/03_plan/agent_tasks/tls_live_bug_fix_restart.md`
- `doc/05_design/scilib_port_architecture.md`
- `doc/08_tracking/bug/lint_val_crash_2026-04-28.md`, `loader_init_sibling_export_2026-04-28.md`, `me_delegator_field_reassign_2026-04-28.md`, `widget_themeid_helper_private_2026-04-28.md`, `recent_bugs.md`, `bug_db.sdn`
- `doc/10_metrics/dashboard/**` (dashboard caches, plans.sdn, spipe_tests.sdn, test_status.sdn, todos.sdn)
- `doc/test/test_db_runs.sdn`, `doc/08_tracking/test/resource_usage.sdn`
- `examples/nvfs/src/driver/fs_driver_impl.spl`, `examples/nvfs/src/posix/fs_driver_impl.spl` (these belong to a separate parallel /dev track)
- `examples/simple_os/arch/x86_64/tls_unit_entry.spl`
- `src/compiler_rust/**` (entire Rust seed subtree — separate compiler-team track)
- `src/compiler/30.types/type_layout.spl`, `src/compiler/90.tools/**` (compiler-team track)
- `src/app/io/cli_commands.spl`, `src/app/llm_dashboard/gui/html_views.spl`, `src/app/sdn/commands.spl`, `src/app/task/main.spl`, `src/app/unreal_cli/main.spl`, `src/app/bug_gen/main.spl`, `src/app/simple_portal/{content_db,server}.spl`
- `src/lib/common/json/builder.spl`, `src/lib/common/ui/**` (UI/theme work)
- Anything not under the §5.2 allowlist regex.

If the per-commit verification in §5.1 finds any of these, the Phase 8 plan is BLOCKED until upstream phases produce clean commits.

---

## 6. Post-Push Verification

Run all four checks. All four must PASS or §7 rollback engages.

### 6.1 Commits landed on origin/main

```bash
cd /home/ormastes/dev/pub/simple
git fetch origin
git log origin/main --since="1 hour ago" --oneline | grep -E 'dbfs|DBFS' | head -20
# Expected: matches the 6–9 commits from §2
```

### 6.2 File-count guard (post)

Already covered in §4.3; record the after-count in `state.md > Phase Outputs > 8-ship`.

### 6.3 Smoke tests against fresh remote tip

After a successful push the local tree at `test/dbfs/` and `src/lib/nogc_sync_mut/db/` is already byte-identical to `origin/main` (we pushed our HEAD). **Do NOT** run `git checkout origin/main -- <paths>` to "freshen" the tree — that command overwrites the working tree and can clobber edits a parallel agent (Phase 5 finalizer, /dev tracks) is making in unrelated directories (per `feedback_jj_uncommitted_clobbered_by_parallel`).

Run smoke directly against the local tree:

```bash
cd /home/ormastes/dev/pub/simple
bin/simple test test/dbfs/dbfs_capability_spec.spl
bin/simple test test/dbfs/dbfs_driver_spec.spl
bin/simple test test/dbfs/mount_table_dbfs_dispatch_spec.spl
bin/simple test test/dbfs/bench_harness_smoke_spec.spl
bin/simple test test/dbfs/dbfs_engine_pager_spec.spl
# Aggregate (full suite):
bin/simple test test/dbfs/
```

If true isolation against `origin/main` is required (e.g. to rule out local dirty-tree interference in failure triage), reuse the §4.2 worktree pattern:

```bash
WORK=$(mktemp -d)
git worktree add --detach "$WORK" origin/main
(cd "$WORK" && bin/simple test test/dbfs/)
git worktree remove "$WORK"
```

Mode: **interpreter only** (per `feedback_compile_mode_false_greens` — no `--mode=native`/`--mode=smf`). Expected: ≥120 it-blocks pass, zero failures, zero `it-block count = 0` silent-greens.

### 6.4 Non-regression on neighbour FS drivers

```bash
bin/simple test src/os/kernel/fs/   # FAT32 specs
bin/simple test test/nvfs/          # NVFS public API
bin/simple test test/ramfs/ 2>/dev/null || true
```

Pre-existing-passing specs must still pass. Per `verify_plan.md §4`.

---

## 7. Rollback Procedure

If Phase 7 surfaces a blocker AFTER some commits already pushed (e.g. a smoke test in §6 fails on `origin/main`), follow this sequence. **NEVER force-push to main** (CLAUDE.md hard rule).

### 7.1 Identify pushed DBFS commits

```bash
cd /home/ormastes/dev/pub/simple
git fetch origin
git log origin/main --since="2 hours ago" --oneline | grep -E 'dbfs|DBFS' \
  > /tmp/dbfs_pushed.txt
cat /tmp/dbfs_pushed.txt
```

### 7.2 Revert in reverse dependency order

`git revert` creates new commits that undo the originals — safe for shared `main`. Revert in REVERSE push order (newest first) so each revert applies cleanly:

```bash
cd /home/ormastes/dev/pub/simple
# Newest-first SHAs from /tmp/dbfs_pushed.txt
for SHA in $(awk '{print $1}' /tmp/dbfs_pushed.txt); do
  git revert --no-edit "$SHA"
done
# This produces N revert commits; each touches only the same allowlist files
# as the original (forbid-list invariant preserved automatically).
sj bookmark set main -r @- && sj git push --bookmark main
```

### 7.3 Subset rollback (preferred when only one batch is bad)

If only one of the 6–9 commits is bad (e.g. only the bench-results commit), revert that single SHA — leave the others in place. Phase 7 then reissues just that batch.

```bash
git revert --no-edit <single-bad-sha>
sj bookmark set main -r @- && sj git push --bookmark main
```

### 7.4 Forbidden rollback techniques

- `git push --force` to main — FORBIDDEN per CLAUDE.md.
- `git reset --hard origin/main~N` followed by force-push — FORBIDDEN.
- `jj abandon` of pushed commits — abandons locally but does not retract from `origin/main`; pointless and misleading.

### 7.5 Post-rollback

After every revert push, re-run §4.3 file-count guard and §6.4 non-regression. Update `state.md > Phase Outputs > 8-ship` with rollback record (which SHAs reverted, why, route-back phase).

---

## 8. Release-Notes Seed

Drop the paragraph below into the PR description, release entry, or CHANGELOG (per the Release Skill `Step 3 — Update CHANGELOG`).

> **DBFS — Database-Backed Filesystem (initial landing).** Adds DBFS as a new `FsDriver` variant alongside `Fat32`, `Nvfs`, `NvfsPosix`, and `RamFs`. DBFS is authoritative for namespace and metadata via an embedded SQLite-class MVCC engine (~2.8 KLoC: pager, namespace B-tree, WAL, checkpoint ring, intent log, recovery, txn manager, schema with 11 tables) and stores file content as page-aligned blobs/extents. The driver plugs in at the existing `DriverInstance` / `MountTable` seam — six surgical edits (`instance.spl`, `mount_table.spl`, `__init__.spl`, new `dbfs_stub.spl`, `capability.spl`, `vfs_init.spl`) — and is mounted at `/data` behind the `dbfs_kernel_linked` feature flag while root stays FAT32. NVFS is refactored toward a pluggable `BlobBackend` so DBFS can ride on raw NVMe arenas or NVFS-managed arenas; direct hardware accessibility (NVMe/PCI/virtio) is preserved through the existing driver framework. Crash safety is covered by WAL + checkpoint-ring + intent-log persistence with a power-cut harness exercising eight failure scenarios (F1–F8). Coverage: 18 specs (~120+ it-blocks) + bench harness with four workloads (metadata-storm, append-log, random-overwrite, mmap-read). No new `rt_*` externs were added, so no compiler bootstrap is required for downstream consumers.

If AC-4 or AC-10 deferred (per §1.4), append:

> Known follow-ups: `fr_dbfs_nvfs_blob_backend` (NVFS arena BlobBackend wiring — depends on `std.storage.nvfs_arena` import path) and `fr_dbfs_migration_plan` (FAT32→DBFS data migration). Both filed under `doc/08_tracking/bug/`.

---

## Quick Reference (5-minute mechanical execution)

```bash
# 1. Gate
test -f .sstack/dbfs-integration/state.md && \
  grep -E '^- \[x\] (1-dev|2-research|3-arch|4-spec|5-implement|6-refactor|7-verify)' \
  .sstack/dbfs-integration/state.md | wc -l   # expected: 7

# 2. Externs check (expected: 0 lines)
grep -REn 'extern[[:space:]]+fn[[:space:]]+rt_' src/lib/nogc_sync_mut/db/ test/dbfs/ | wc -l

# 3. Allowlist verify (expected: 0 forbid-list hits per commit)
ALLOW='^(src/lib/nogc_sync_mut/db/|test/dbfs/|src/lib/nogc_sync_mut/fs_driver/(instance|mount_table|__init__|dbfs_stub|capability)\.spl$|src/os/services/vfs/vfs_init\.spl$|doc/04_architecture/dbfs_architecture\.md$|\.sstack/dbfs-integration/|doc/06_spec/dbfs/|doc/08_tracking/bug/fr_dbfs_)'
for SHA in $(git log origin/main..@ --reverse --pretty=%H); do
  git show --name-only --pretty='' "$SHA" | grep -vE "$ALLOW" && echo "BLOCK: $SHA"
done

# 4. File-count before (committed tree only — never `git ls-files`)
BEFORE=$(git ls-tree -r --name-only HEAD | wc -l)

# 5. Push
sj bookmark set main -r @- && sj git push --bookmark main

# 6. File-count after + smoke
git fetch origin
AFTER=$(git ls-tree -r --name-only origin/main | wc -l)
[ "$AFTER" -ge "$BEFORE" ] || echo "ABORT — see §7"
bin/simple test test/dbfs/

# 7. Record in state.md > 8-ship: SHAs pushed, file counts, smoke results
```
