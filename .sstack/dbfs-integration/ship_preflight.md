# Phase 8 Ship Pre-Flight: dbfs-integration

**Run date:** 2026-04-28
**Run by:** Phase 8 ship-preflight agent (read-only, advisory)
**HEAD at run time:** `063ff4ba29` (`docs(dbfs): module cross-ref header in dbfs_engine/__init__`)
**Mode:** READ-ONLY. No `.spl`, no `state.md`, no doc, no VCS write op was performed.
**Phase 6 status at run time:** ACTIVE — Phase 6 (refactor) was committing concurrently while these checks ran.

---

## Verdict at a glance

> **READY TO SHIP: RED — BLOCKED.**

Three independent hard blockers, any one of which alone is a stop. **Root cause of the contamination is Phase 6's commit hygiene**: all three catastrophically dirty commits (`8577384082`, `68bb523eec`, `063ff4ba29`) are Phase 6 outputs, created with `jj commit -m "…"` against a worktree that already had `M`-state files from 6+ other tracks. Phase 6 is **still running**, so every additional commit it produces will inherit the same dirty tree unless it switches to file-scoped `git add <explicit files>; git commit` (or `jj commit <paths>`). Do **not** push.

| # | Blocker | Severity |
|---|---------|---------|
| B1 | `.git/index.lock` (3.0 MB) is held; `jj op log` errors with "Failed to reset Git HEAD state" | HARD STOP — VCS unusable |
| B2 | 3 of 7 local commits include forbid-list files (1 catastrophic: `8577384082` ships ~30 unrelated files including `src/compiler_rust/**`, MCP, kernel-IPC, loader, code_quality, compiler stats) | HARD STOP — would ship cross-track contamination |
| B3 | `state.md > Phase Checklist` shows `5-implement / 6-refactor / 7-verify / 8-ship` all `[ ]`; AC checkbox section disagrees with phase checklist; Phase 7 `<pending>` and §7 sign-off boxes unchecked | HARD STOP — Phase 7 has not run; gate §1.2 fails |
| B7 | **Phase 6 is still using whole-worktree `jj commit -m`** — every new commit it produces will inherit the dirty tree of unrelated tracks. Operator must instruct Phase 6 to switch to file-scoped staging BEFORE preflight is re-run, or any cleanup will be invalidated by the next Phase 6 commit. | HARD STOP — feedback loop |

---

## Per-check report

### 1. AC checklist verification — **WARN (inconsistent)**

`state.md > Acceptance Criteria` (declarative section) all 10 are `[ ]` (the original task statement is unchecked).

`state.md > Phase Outputs > 5-implement > AC Checkbox Status` has TWO copies of the AC status (the search returned both), and they disagree:

- "current" (top of section, dated 2026-04-28): 9× `[x]`, 1× `[~]` (AC-6 PARTIAL — block-layer plug-through gap, see hw_passthrough_audit.md)
- "earlier" (lower in section): AC-1 `[ ]`, AC-2 `[x]`, AC-3 `[x]`, AC-4 `[ ]`, AC-5 `[x]`, AC-6 `[x]`, AC-7 `[x]`, AC-8 `[x]`, AC-9 `[x]`, AC-10 `[ ]`.

Net: even on the optimistic read, AC-6 is `[~]`, the original AC list is still all `[ ]`, and AC-4 / AC-10 require a hard-blocker decision per `ship_plan §1.4` (Option A land code OR Option B file FR doc). That decision has **not** been recorded in `state.md > 8-ship` (`<pending>`).

**[FAIL]** — gate §1.1 (10 ACs) is not provably green; gate §1.4 (AC-4 / AC-10 decision tree) has no recorded decision.

### 2. Externs sanity — **PASS**

```
grep -REn 'extern[[:space:]]+fn[[:space:]]+rt_' \
  src/lib/nogc_sync_mut/db/ test/dbfs/ | wc -l
→ 0
```

Matches `ship_plan §3.1` expected = 0. R10 (`feedback_extern_bootstrap_rebuild`) does NOT trigger — bootstrap is not required for ship.

**[PASS]** — 0 new `rt_*` externs in DBFS scope.

### 3. Allowlist diff scope — **PASS (DBFS-allowlist totals)**

`git diff origin/main --stat -- '<allowlist globs>'`:

- 29 files
- +1940 / −482 LoC

All changes are under `src/lib/nogc_sync_mut/db/{dbfs_driver,dbfs_engine}/`, `src/lib/nogc_sync_mut/fs_driver/{instance,mount_table,fat32_stub}.spl`, and `test/dbfs/**`. No `.sstack/` or `doc/04_architecture/dbfs_architecture.md` change is present in the un-pushed diff (those files exist on disk but are not in the un-pushed commits — they may have been pushed earlier).

**[PASS]** — DBFS-scope diff is bounded as expected.

### 4. Forbid-list check — **FAIL (catastrophic)**

The full un-pushed diff lists ~50 file paths. The non-allowlist subset includes (forbid-list per `ship_plan §5.3`):

- `bin/codex_chrome_devtools_mcp.cmd`, `bin/codex_stitch_mcp.cmd`, `bin/simple_lsp_mcp_server.cmd`, `bin/simple_mcp_server.cmd`, `bin/t32_lsp_mcp_server.cmd`, `bin/t32_mcp_server.cmd`
- `scripts/setup.cmd`, `src/compiler_rust/vendor/zerocopy/win-cargo.bat`
- `src/compiler/90.tools/stats/db_aggregator.spl`, `src/compiler/90.tools/stats/dynamic.spl`
- `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl`
- `src/app/cli/fix_dbs.spl`
- `src/lib/common/js/engine/{interpreter,runtime}.spl`, `src/lib/common/json/builder.spl`, `src/lib/common/tooling/easy_fix/rules_lint.spl`
- `src/lib/log.spl`, `src/lib/text.spl`
- `src/lib/nogc_async_mut/mcp/{bugdb_resource,resources}.spl`
- `src/os/posix/process_compat.spl`, `src/os/services/fat32/fat32.spl`, `src/os/services/llm/mcp_os_server.spl`, `src/os/services/vfs/{mod,vfs,nvfs_connector}.spl`, `src/os/tls13/{hkdf,record13}.spl`
- `examples/simple_os/arch/x86_64/os_entry.spl`
- `doc/test/test_db_runs.sdn`
- `test/code_quality/{chars_deprecated,deprecated_removed}_spec.spl` + matchers
- `test/feature/app/database_resource_spec.spl` + matcher
- `test/system/.spipe_matchers_os_tls_spec.spl`
- `test/unit/app/mcp_unit/bugdb_resource_semantics_spec.spl` + matcher
- `test/unit/compiler/{stats_bug_schema_spec.spl, .spipe_matchers_stats_bug_schema_spec.spl}`
- `test/unit/lib/.spipe_matchers_log_facade_backend_swap_spec.spl`, `test/unit/lib/common/{js_runtime_host_property_spec.spl, .spipe_matchers_js_*}.spl`
- `test/unit/os/services/init/init_service_spec.spl`
- `test/unit/os/process_spawn_abi_spec.spl` + matchers
- `test/unit/os/kernel/ipc/{spawn_binary_argv_spec, spawn_binary_kernel_abi_spec}.spl` + matchers
- `test/unit/os/kernel/loader/process_image_spec.spl` + matcher

Per-commit attribution (which commits would ship the contamination):

| Commit | Subject | Off-allowlist files | Status |
|--------|---------|---------------------|--------|
| `1469ab3bce` | `feat(dbfs): add module-level persistent store to DbFsDriver` | 0 | CLEAN |
| `153ee4868b` | `feat(dbfs): add RAM-backed FAT32 test fixture; rename VfsMountEntry` | 4 (`src/os/services/{fat32/fat32, llm/mcp_os_server, vfs/mod, vfs/vfs}.spl`) | **PROBABLY LEGITIMATE** — these are the rename-ripple consumers of `VfsMountEntry`; either widen `ship_plan §5.2` allowlist to cover the rename consumers OR split the rename into its own commit. Triage required, but not the same class as the `8577384082` catastrophe. |
| `6ecc3d9a12` | `test(dbfs): add dbfs integration spec suite (Phase 5)` | 0 | CLEAN |
| `0f714ccb7b` | `test(dbfs): add spipe matchers for nvfs_no_regression spec` | 0 | CLEAN |
| `8577384082` | `refactor(dbfs): extract resolve helpers in dbfs_driver` (Phase 6 §7 item 1) | **~30** (compiler_rust, MCP, kernel IPC, loader, code_quality, compiler stats, fix_dbs, etc.) | **CATASTROPHIC** — Phase 6 commit |
| `68bb523eec` | `refactor(dbfs): extract single-key scan helper in schema` (Phase 6 §7 item 4) | 6 (`examples/simple_os/arch/x86_64/os_entry.spl`, `src/os/services/vfs/nvfs_connector.spl`, `src/os/tls13/{hkdf,record13}.spl`, `test/system/.spipe_matchers_os_tls_spec.spl`, `test/unit/os/services/init/init_service_spec.spl`) | DIRTY — Phase 6 commit |
| `063ff4ba29` | `docs(dbfs): module cross-ref header in dbfs_engine/__init__` (Phase 6 §7 item 3) | 3 (`src/os/services/vfs/nvfs_connector.spl`, `test/unit/compiler/.spipe_matchers_stats_bug_schema_spec.spl`, `test/unit/os/services/init/init_service_spec.spl`) | DIRTY — Phase 6 commit |

Root cause matches `feedback_jj_uncommitted_clobbered_by_parallel` and `feedback_wip_snapshot_half_ship`: parallel agents kept the working tree dirty with files from other tracks, and `jj commit -m "refactor(dbfs): …"` snapshotted the entire dirty worktree into commit `8577384082`. The same mechanism happened on a smaller scale for `153ee4868b`, `68bb523eec`, `063ff4ba29`.

**[FAIL]** — pushing as-is would publish ~30+ files belonging to 5+ unrelated tracks (compiler-team Rust seed, MCP, TLS, kernel IPC, loader, code_quality, browser/JS engine, scilib, …) as part of a "dbfs-integration" ship.

### 5. WIP-snapshot defense — **FAIL**

This is the same finding as §4, viewed differently. Even the "clean" commits 1469ab3b / 6ecc3d9a / 0f714ccb individually look fine, but the chain as a whole still ships forbid-list files because commits 153e/8577/68bb/063f got polluted. Cherry-picking only the 3 clean commits would lose the schema-helper refactor and the cross-ref header docs.

**[FAIL]** — half-baked subset is the dominant signal.

### 6. Local commit count — **PASS (with shape note)**

7 local commits ahead of `origin/main`:

```
063ff4ba29 docs(dbfs): module cross-ref header in dbfs_engine/__init__
68bb523eec refactor(dbfs): extract single-key scan helper in schema
8577384082 refactor(dbfs): extract resolve helpers in dbfs_driver
0f714ccb7b test(dbfs): add spipe matchers for nvfs_no_regression spec
6ecc3d9a12 test(dbfs): add dbfs integration spec suite (Phase 5)
153ee4868b feat(dbfs): add RAM-backed FAT32 test fixture; rename VfsMountEntry
1469ab3bce feat(dbfs): add module-level persistent store to DbFsDriver
```

Verified the engine batch is **already on origin/main**:

```
$ git log origin/main --oneline -- src/lib/nogc_sync_mut/db/dbfs_engine/
97380b799e fix(test): SDN coverage specs import via std.sdn.* not lib.sdn.*
[engine landing commit older than this — engine modules present in tree]

$ git ls-tree -r --name-only origin/main -- src/lib/nogc_sync_mut/db/dbfs_engine/
__init__.spl, checkpoint.spl, checkpoint_ring.spl, intent_log.spl,
ns_btree.spl, pager.spl, recovery.spl, schema.spl, txn.spl, wal.spl
(10 modules, identical to HEAD)
```

So `ship_plan §2` batches 1 (engine) and 4 (architecture doc + state.md) are already on origin. The 7 un-pushed commits cover batches 2 (driver), 3 (tests), and 5 (refactor) — chain shape is consistent with `ship_plan §2`, just split differently than predicted (driver landed in 2 commits, tests in 2 commits, refactor in 3 commits).

**[PASS]** — engine batch on origin; un-pushed chain covers driver + tests + refactor as expected.

### 7. `.git/index.lock` — **FAIL**

```
-rw-rw-r-- 1 ormastes ormastes 3079378 Apr 28 11:06 /home/ormastes/dev/pub/simple/.git/index.lock
```

3.0 MB, exists at run-time. Caused `jj op log` to error with:
```
Error: Failed to reset Git HEAD state
Caused by:
  1: Could not acquire lock for index file
  2: The lock for resource '.git/index' could not be obtained …
     The lockfile … might need manual deletion.
```

Phase 6 (concurrent) is the most likely holder. Operator must verify Phase 6 has finished AND no other agent is mid-`jj`, then either wait or clear per `feedback_push_via_worktree` (worktree cherry-pick fallback in `ship_plan §4.2`).

**[FAIL]** — VCS write/read ops are blocked until lockfile clears.

### 8. JJ op log — **FAIL (consequence of #7)**

`jj op log` errors as above. `jj op log --ignore-working-copy` returns: 6× `snapshot working copy` (recent ops are all snapshots — Phase 6 is busy). No "in-progress" markers, but the lock is in place. Cannot confirm whether the most recent op completed cleanly.

**[FAIL]** — defer until #7 clears.

### 9. DBFS interpreter test sanity — **PASS (binary present)**

```
-rwxrwxr-x 1 ormastes ormastes 4680 /home/ormastes/dev/pub/simple/bin/simple
```

Exists, 4.6 KB shell wrapper (per `feedback_simple_run_wrapper_broken` it surfaces real errors on stderr as of 2026-04-25 / B1). Phase 7 (when it runs) can use it. We did not invoke tests.

**[PASS]** — runner present.

### 10. Architecture doc presence — **PASS**

```
-rw-rw-r-- 1 ormastes ormastes 32177 /home/ormastes/dev/pub/simple/doc/04_architecture/dbfs_architecture.md
```

32 KB, dated 2026-04-28 02:17. Section header confirms D1 reuse decision + D2 gap list. Likely already on `origin/main` (no diff in §3).

**[PASS]** — present, non-empty, recent.

### 11. `state.md` phase checklist — **FAIL**

```
- [x] 1-dev          — 2026-04-28
- [x] 2-research     — 2026-04-28
- [x] 3-arch         — 2026-04-28
- [x] 4-spec         — 2026-04-28
- [ ] 5-implement
- [ ] 6-refactor
- [ ] 7-verify
- [ ] 8-ship
```

5-implement is unchecked despite the AC checkbox section claiming all 10 ACs `[x]` / `[~]`. 6-refactor unchecked but Phase 6 is concurrently committing. 7-verify unchecked AND `Phase Outputs > 7-verify` is `<pending>` AND `verify_plan §7` sign-off boxes are all `[ ]`. Phase 7 has not run. Per `ship_plan §1.2`, all 8 boxes in §7 must be ticked before ship — they are 0/8.

**[FAIL]** — Phase 7 is not done; this is a hard ship gate.

### 12. Risk register checkpoint — **FAIL (Top-3 not all mitigated)**

Per `risk_premortem.md > Pre-mortem Top 3 — fix-before-ship`:

| Risk | Status at preflight |
|------|---------------------|
| **R11** Compile-mode false-greens (UNREGISTERED in D12) | NOT mitigated. `verify_plan §0.1` would catch any `--mode=native/--mode=smf` invocation, but Phase 7 hasn't run, so the grep has not happened. State.md does NOT confirm interpreter-only execution. |
| **R13** BlobBackend conformance suite missing a backend variant (UNREGISTERED in D12) | NOT mitigated. The recommended `test/dbfs/arena_conformance_suite.spl` is not present in the §3 allowlist diff. |
| **R1** Intent-log disk persistence (HIGH, registered) | UNCLEAR. `state.md > 4-spec > Phase 5 Prerequisites (flagged)` lists "intent_log + checkpoint_ring persistence" as a prerequisite that must be **cleared** before ship. State.md does not record whether it has been cleared. `dbfs_engine_intent_log_spec.spl` claims pass but per `verify_plan §1.AC-3` and `§7`, the prerequisite-cleared status must be explicitly recorded — it is not. |

Plus `state.md > 4-spec > Phase 5 Prerequisites (flagged)` lists 9 module/method prerequisites (NvfsArena, RawNvmeArena, BlockDevice helpers, `Capability.Txn` variant, …). Status of each is not stated in 5-implement.

**[FAIL]** — at least R11 and R13 are not mitigated; R1 cannot be confirmed mitigated without explicit Phase 7 sign-off.

---

## Summary table

| # | Check | Result |
|---|-------|--------|
| 1 | AC checklist | FAIL |
| 2 | Externs (rt_*) | PASS |
| 3 | Allowlist diff scope | PASS |
| 4 | Forbid-list check | FAIL |
| 5 | WIP-snapshot defense | FAIL |
| 6 | Local commit count | PASS (engine on origin confirmed) |
| 7 | `.git/index.lock` clean | FAIL |
| 8 | JJ ops not in-progress | FAIL |
| 9 | `bin/simple` present | PASS |
| 10 | dbfs_architecture.md | PASS |
| 11 | state.md phase checklist | FAIL |
| 12 | Risk register top-3 | FAIL |

**Score: 5 PASS / 7 FAIL**

---

## Ready-to-ship verdict: **RED**

### Blockers (must clear in upstream phases before any push)

1. **B7 (FIRST — fix this before B1–B6, otherwise cleanup will be invalidated) — Tell Phase 6 to switch to file-scoped commits.** Phase 6 is currently running and using `jj commit -m "…"` against the dirty whole worktree. Every additional commit it produces will inherit the same cross-track contamination. Operator MUST instruct Phase 6 to either:
   - use `jj commit <explicit-paths>` per commit, OR
   - use `git add <explicit-paths>; git commit -m "…"` (then `jj git import`), OR
   - pause Phase 6, clean the worktree (commit/stash dirty unrelated files to their own tracks), then resume.
   Until B7 is fixed, do not start B1–B6 cleanup — the next Phase 6 commit will undo it.
2. **B1 — Index lock held.** `.git/index.lock` blocks all VCS reads and writes. Operator must wait for Phase 6 to finish, confirm no `jj` op is mid-flight, then re-run preflight. Do NOT delete the lockfile while another agent is running (`feedback_submodule_race_parallel_dev`).
3. **B2 — Commits `8577384082`, `68bb523eec`, `063ff4ba29` ship forbid-list files; `153ee4868b` needs allowlist triage.** Phase 6's three commits are the catastrophic ones. `153ee4868b` is *probably legitimate* (rename ripple of `VfsMountEntry`) — either widen `ship_plan §5.2` allowlist OR split the rename into its own commit. The Phase 6 commits must be either:
   - rebased into a 1-file commit (only `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` for `8577384082`) via `git worktree` cherry-pick (`feedback_push_via_worktree`), discarding the unrelated paths, OR
   - dropped entirely and the Phase 6 refactor work re-authored on a clean tree (after B7 lands).
4. **B3 — Phase 7 has not run.** `state.md > 7-verify` is `<pending>`; `verify_plan §7` sign-off is 0/8. Per `ship_plan §1.2`, all 8 boxes must be ticked. Run Phase 7 first.
5. **B4 — `state.md` phase checklist out of sync.** Even if Phase 6 finishes mid-preflight, the headline phase checklist (`5-implement [ ]`, `6-refactor [ ]`, `7-verify [ ]`) contradicts the AC checkbox section. Update `state.md` so the phase checklist reflects truth before the ship gate runs.
6. **B5 — AC-4 / AC-10 hard-blocker decision unrecorded.** Per `ship_plan §1.4`, choose Option A (land code) or Option B (file FR doc) for AC-4 (NVFS BlobBackend) and AC-10 (migration plan), and record the decision in `state.md > 8-ship` BEFORE push.
7. **B6 — Risk-register Top-3 not mitigated.** R11 (compile-mode false-greens) requires the `verify_plan §0.1` grep to be run and recorded. R13 (BlobBackend conformance suite) requires `test/dbfs/arena_conformance_suite.spl` to be added (or explicitly waived in the risk register). R1 (intent-log persistence) requires Phase-5-prereq-cleared statement in `state.md`.

### Warnings (not blockers, but watch)

- Engine batch is confirmed on `origin/main` (10 modules in `src/lib/nogc_sync_mut/db/dbfs_engine/`, identical between HEAD and origin). `ship_plan §2` batch 1 already shipped.
- `migration_playbook.md` (24 KB) and `hw_passthrough_audit.md` (22 KB) and `posix_compat_matrix.md` (20 KB) all exist under `.sstack/dbfs-integration/`. They are not in the un-pushed diff. If they are local-only (never committed), they are at risk of being lost on a `jj` reconcile (`feedback_jj_uncommitted_clobbered_by_parallel`).
- The "double" AC-checkbox-status block in `state.md > 5-implement` should be deduplicated; it currently presents two contradictory snapshots.
- `ship_plan §"Quick Reference (5-minute mechanical execution)"` claim is **invalidated by current state**. Realistic time is 60–90 min cleanup-then-ship; if Phase 6 must redo the refactor commits with clean staging, add another 30 min.

---

## Phase 8 execution order — **DO NOT RUN until B1–B6 clear**

When all six blockers above are cleared, run the ship_plan `Quick Reference (5-minute mechanical execution)`:

```bash
cd /home/ormastes/dev/pub/simple

# 0. Re-run THIS preflight; require RED → GREEN before continuing.

# 1. Gate (expect 7 phases [x])
test -f .sstack/dbfs-integration/state.md && \
  grep -E '^- \[x\] (1-dev|2-research|3-arch|4-spec|5-implement|6-refactor|7-verify)' \
  .sstack/dbfs-integration/state.md | wc -l   # expected: 7

# 2. Externs check (expected: 0)
grep -REn 'extern[[:space:]]+fn[[:space:]]+rt_' \
  src/lib/nogc_sync_mut/db/ test/dbfs/ | wc -l

# 3. Allowlist verify (expected: every commit clean)
ALLOW='^(src/lib/nogc_sync_mut/db/|test/dbfs/|src/lib/nogc_sync_mut/fs_driver/(instance|mount_table|__init__|dbfs_stub|capability)\.spl$|src/os/services/vfs/vfs_init\.spl$|doc/04_architecture/dbfs_architecture\.md$|\.sstack/dbfs-integration/|doc/06_spec/dbfs/|doc/08_tracking/bug/fr_dbfs_)'
for SHA in $(git log origin/main..@ --reverse --pretty=%H); do
  echo "=== $SHA ==="
  git show --name-only --pretty='' "$SHA" | grep -vE "$ALLOW" \
    && echo "BLOCK: $SHA off-allowlist" \
    || echo "  OK"
done

# 4. File-count guard before
BEFORE=$(git ls-tree -r --name-only HEAD | wc -l)

# 5. Push (jj wrapper)
sj bookmark set main -r @- && sj git push --bookmark main

# 6. File-count guard after + smoke
git fetch origin
AFTER=$(git ls-tree -r --name-only origin/main | wc -l)
[ "$AFTER" -ge "$BEFORE" ] || { echo "ABORT — see ship_plan §7"; exit 1; }
bin/simple test test/dbfs/

# 7. Record SHAs / file counts / smoke result in state.md > 8-ship
```

If `sj` is locked (`feedback_push_via_worktree`), use the worktree cherry-pick fallback per `ship_plan §4.2`.

---

## Phase 8 estimated time

- If B1–B6 clear in ≤ 1 round of cleanup: **30–45 min** (Phase 7 verify + state.md updates + commit-chain rewrite of `8577384082` + `153ee4868b` + `68bb523eec` + `063ff4ba29` + push). Mechanical ship itself is still ~5 min once preflight is GREEN.
- If `8577384082` cannot be safely rebased and the resolve-helper refactor must be re-authored: add 30–60 min for Phase 6 re-do.
- Realistic total before any push lands cleanly: **60–90 min** from preflight RED → GREEN.

---

## Cross-references

- `ship_plan.md §1` (gate), `§2` (commit chain), `§3` (externs), `§5.2/5.3` (allow/forbid lists), `§4.3` (file-count guard)
- `risk_premortem.md` Top-3 fix-before-ship: R11, R13, R1
- `verify_plan.md §0.1` (compile-mode grep), `§7` (sign-off boxes)
- Memory: `feedback_jj_uncommitted_clobbered_by_parallel`, `feedback_wip_snapshot_half_ship`, `feedback_push_via_worktree`, `feedback_submodule_race_parallel_dev`, `feedback_destructive_upstream_detection`, `feedback_extern_bootstrap_rebuild`
