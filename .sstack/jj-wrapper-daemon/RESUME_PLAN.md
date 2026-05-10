# Resume Plan — `jj-wrapper-daemon` (sj VCS service)

> ## ⚠️ READ §11e FIRST
>
> A parallel claude session likely ran `git clean -fd` (or similar) during
> this session. Most untracked work disappeared. The Rust externs survived
> and compile clean. State.md and this file survived. Everything else needs
> recovery or rebuild — see §11e for the inventory and three recovery options.
> **Coordinate with any parallel claude sessions before resuming.**


> **Purpose:** Detailed restart guide so a future session can pick up exactly
> where this one paused. Read this top-to-bottom before doing anything.
>
> **Pause point:** End of Phase 3 (arch). Phase 4 (spec) was about to start
> when the user paused to write this resume doc.
>
> **Date paused:** 2026-04-26
> **Owner:** Yoon, Jonghyun (ormastespq@gmail.com)
> **Branch:** `main` (per `.claude/rules/vcs.md` — never branch)

---

## 0. How to restart

1. `cd /home/ormastes/dev/pub/simple`
2. Read this file end-to-end.
3. Read `.sstack/jj-wrapper-daemon/state.md` (1041 lines, full design context).
4. Read `doc/04_architecture/sj_vcs_service.md` (431 lines, durable design).
5. Run the SStack pipeline from **Phase 4** by invoking
   `/dev` (or `/sstack`) with the same prompt that started this work, or
   directly spawn the Phase-4 agent following the recipe in §6 below.
6. Verify the local jj/git state is unchanged from §3 before any code lands.

**One-liner restart prompt to feed to /dev:**

> resume `.sstack/jj-wrapper-daemon` — Phase 1/2/3 are complete. Read
> `RESUME_PLAN.md` and `state.md`, then start Phase 4 (spec) per the recipe.

---

## 1. What this feature is

A unified per-repo VCS service replacing ad-hoc `jj`/`git` calls. Two layers:

1. **`std.service` daemon base** at `src/lib/nogc_sync_mut/service/`
   (PID file + liveness, UDS JSON request/response, FIFO queue with priority
   lanes, cooperative SIGTERM shutdown).
2. **`simple_vcs_daemon`** + **`bin/sj` CLI** built on top, exposing both
   jj-native verbs and a git-CLI mimic surface, with lease-based locking,
   ghost-lock reclaim, max-hold kill, and a `gg → sj git` shim.

**Architecture:** **MDSOC+** (MDSOC outer + ECS business layer, locked).

**Acceptance criteria:** AC-1..AC-7 in `state.md` lines 32–73. All seven must
be verifiable by green BDD specs at the end of Phase 7.

---

## 2. Current phase status

| # | Phase | Status | Output location | Notes |
|---|-------|--------|-----------------|-------|
| 1 | dev | ✅ done | `state.md` lines 75–95 (constraints + decisions) | User confirmed `gg≡git`, `bin/sj`, per-repo scope, MDSOC+ |
| 2 | research | ✅ done | `state.md` `## Phase 2 Research — R-A/B/C/D` sections | 4 parallel Sonnet sub-agents, disjoint scope |
| 3 | arch | ✅ done | `state.md` `### 3-arch` lines 403–617 + `doc/04_architecture/sj_vcs_service.md` | 11 ADRs, MDSOC+ capsule diagram, ECS table |
| 4 | spec | 🔲 **NEXT** | `state.md` `### 4-spec` line 618 (currently `<pending>`) | See §6 below for full restart recipe |
| 5 | implement | 🔲 pending | 4 parallel sub-agents I-A/B/C/D — see §7 | Critical path: I-A's UDS externs |
| 6 | refactor | 🔲 pending | tech-lead `/refactor` + `/simplify` pass | — |
| 7 | verify | 🔲 pending | full QA gate — AC-1..AC-7 sign-off | — |
| 8 | ship | 🔲 pending | per-phase commits, push via worktree if jj contended | — |

---

## 3. Repo state at pause

- **Branch:** `main` (jj `@`)
- **Uncommitted files at pause:** 74 (per `git status --porcelain | wc -l`)
  — most predate this feature (B4-sugar WIP, bignum, BDD runtime, ssh, etc).
  See `git status` for the inventory.
- **New files added by this feature:**
  - `.sstack/jj-wrapper-daemon/state.md` (1041 lines, untracked)
  - `.sstack/jj-wrapper-daemon/RESUME_PLAN.md` (this file)
  - `doc/04_architecture/sj_vcs_service.md` (431 lines, untracked)
- **No code under `src/` was touched by this feature yet** — Phase-3 was
  pure design. Phase-5 is the first phase that writes `.spl`.
- **Stale `.git/index.lock`:** R-A confirmed a 6.6 MB ghost lock exists in
  this repo right now. It is currently breaking some `jj op log` calls.
  **Decide on restart whether to clear it manually before Phase-7 testing
  or let the daemon's startup-reclaim path exercise it as part of QA.**

---

## 4. Locked decisions (do not relitigate without user OK)

From `state.md` lines 75–95 + 11 ADRs in lines 446–506:

1. **MDSOC+** outer + ECS inner — capsule per concern (lifecycle, server,
   queue, lease, audit, client); business logic as components/systems.
2. **CLI binary name:** `bin/sj` (simple-jj).
3. **Daemon scope:** per-repo. Socket `./.sj/daemon.sock`, PID
   `./.sj/daemon.pid`, audit `./.sj/audit.log`, stash stack
   `./.sj/stash_stack.json`.
4. **`gg ≡ git`** — AC-5 collapses to a documentation shim
   (`doc/07_guide/quick_reference/sj_cli.md`); R-C found zero
   in-tree command callers.
5. **`jj arrange` does NOT exist** in jj 0.32.0 → `sj git rebase -i` is
   **forbidden** with an educational error pointing at
   `sj split` / `sj squash --into` / `sj rebase --onto` (D-1).
6. **Read-bypass lane** always injects `--ignore-working-copy --no-pager
   --color never`. Canonical read-verb list lives as a constant in
   `jj_exec.spl` (D-2).
7. **BUSY error contract:** exit code **75** (`EX_TEMPFAIL`), stderr prefix
   `ERROR[BUSY]: lease <id> held by pid <pid>, expires <iso8601>` (D-5).
8. **UDS server externs** are net-new: `rt_unix_socket_listen`,
   `rt_unix_socket_accept`, `rt_unix_socket_send`, `rt_unix_socket_recv`,
   `rt_unix_socket_close`. After adding them, run
   `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (per
   memory `feedback_extern_bootstrap_rebuild.md`). Critical-path for I-A.
9. **Ghost `.git/index.lock` reclaim rule:** ALL three AND-ed —
   `lsof` empty AND mtime > 30 s AND no live daemon lease references git.
   Scans `.git/worktrees/*/index.lock` too (D-6).
10. **`sj git push --via-worktree` is opt-in** only (D-7). Daemon eliminates
    contention by construction; auto-fallback adds magic.
11. **Submodule policy:** accept-with-warn + auto-pin (D-8). Exclusive lease
    held across mutation + immediate `git commit --no-verify` to pin the
    160000 gitlink before jj re-snapshots.

---

## 5. Critical risks / flags carried forward

**For the Phase-4 spec writer:**
- D-4 (UDS externs + bootstrap rebuild) is the single critical-path
  dependency for Phase-5 I-A; **service-base BDD specs cannot be
  integration-tested until those externs exist**. Spec must define them as
  expected-to-exist contracts.
- D-1 (`rebase -i` forbidden) → spec needs a BDD case asserting
  `ERROR[FORBIDDEN]` for `sj git rebase -i`, **not** a translation case.
- D-5 BUSY exit-code **75** must be tested against `sync.spl`'s
  `exit_code == 0` branch to confirm no regression before the
  `jj_runner.spl` migration ships.
- D-11 stash stack persistence across daemon restarts is easy to miss —
  `sj git stash` and `sj git stash pop` happen in different invocations.

**Repo-wide pitfalls (from memory):**
- `feedback_compile_mode_false_greens.md` — `--mode=native` and `--mode=smf`
  swallow runtime errors. Run BDD specs in **interpreter mode** until the
  R2-broader fix lands.
- `feedback_class_trait_header_form_also_fails.md` — header-form
  `class X: Trait` does not parse (verified 2026-04-26). Use `impl Trait
  for X { … }` blocks for any trait conformance in I-A/B/C.
- `feedback_extern_bootstrap_rebuild.md` — after adding `rt_*` externs,
  use `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`, **not**
  `bin/simple build bootstrap` (the latter no-ops via wrapper whitelist).
- `feedback_submodule_race_parallel_dev.md` — pause other parallel `/dev`
  runs during Phase-8 ship.

---

## 6. Phase 4 (spec) restart recipe

**Goal:** failing BDD specs covering AC-1..AC-7 + the lease state machine
+ git-mimic translation + concurrency smoke.

**Spawn instruction (give to a fresh general-purpose agent, model = sonnet):**

> You are SStack Phase-4 **spec / QA Lead** for the `jj-wrapper-daemon`
> feature. Read `.sstack/jj-wrapper-daemon/state.md` end-to-end and
> `doc/04_architecture/sj_vcs_service.md`. Write **failing** BDD specs
> only — no implementation. Coverage:
>
> - `test/unit/lib/service/service_lifecycle_spec.spl` — start/stop, PID
>   file lifecycle, SIGTERM graceful shutdown, no PID-file leak (covers
>   the `test_daemon`/`task_daemon` anti-pattern noted in R-B).
> - `test/unit/lib/service/lease_ghost_reclaim_spec.spl` — kill holder,
>   verify reclaim is logged with reason, new lease grants.
> - `test/unit/lib/service/lease_max_hold_spec.spl` — long op exceeds
>   `--max-hold`, daemon SIGTERMs child, surfaces typed `MAX_HOLD` error.
> - `test/unit/app/sj/git_mimic_translation_spec.spl` — table-driven
>   spec covering R-D's translation table; for every row, assert
>   `sj git X` → expected jj invocation **OR** the typed error
>   (`FORBIDDEN` for `rebase -i`, `push` bare, `push --force`,
>   `checkout` bare, `filter-branch`).
> - `test/unit/app/sj/busy_contract_spec.spl` — assert exit code 75 +
>   stderr prefix `ERROR[BUSY]:`; assert `sync.spl`-style
>   `exit_code == 0` branching is unaffected by BUSY errors.
> - `test/unit/app/sj/ignore_working_copy_spec.spl` — assert daemon
>   injects `--ignore-working-copy --no-pager --color never` on every
>   read-bypass-lane verb (canonical list from D-2).
> - `test/system/sj_concurrency_spec.spl` — N=8 concurrent `sj describe`
>   /`sj new` clients; every cmd succeeds or returns BUSY; no orphan
>   `.git/index.lock`; no two mutating ops overlap in audit log.
> - `test/system/sj_ghost_index_lock_spec.spl` — pre-stage a stale
>   `.git/index.lock` (tmpdir, no PID, mtime old enough); assert daemon
>   reclaims it on startup per D-6's three-AND rule.
> - `test/system/sj_stash_persistence_spec.spl` — `sj git stash` →
>   restart daemon → `sj git stash pop` retrieves the entry.
>
> **Constraints:**
> - Use `std.io_runtime`, never `app.io` (per `feedback_test_imports.md`).
> - All BDD body work must run in **interpreter mode** (per
>   `feedback_compile_mode_false_greens.md` until R2-broader lands).
> - `it` blocks: avoid `return` in body (per
>   `feedback_interpreter_test_limits.md`).
> - Do not implement; the specs MUST fail until Phase 5 lands.
> - Use `/sspec` skill if it helps with structure.
>
> **Exit criteria:**
> - Every AC-N is mapped to ≥1 spec
> - Every D-N decision (D-1..D-11) is asserted by ≥1 spec
> - All specs run and fail with a recognizable "not yet implemented"
>   message (not a parse error or import failure)
> - Append a `### 4-spec` summary to `state.md` listing every spec file
>   created with its AC/D coverage; mark Phase 4 done in the checklist
>
> Tools: Bash (small), Read, Write, Edit, ctx-mode family, advisor()
> (call once after drafting the spec list, before writing the first file).

---

## 7. Phase 5 (implement) restart recipe — 4 parallel agents

Spawn all four in **one message** with parallel `Agent` tool calls
(per `feedback_parallel_sonnet.md`). Each gets a disjoint file scope
(per `feedback_parallel_scope_partition.md`) and an explicit advisor()
nudge (per `feedback_subagent_advisor_access.md`).

### I-A — service base + UDS externs (CRITICAL PATH, blocks I-B)

**Scope:**
- `src/runtime/uds.rs` (new) — implement the 5 `rt_unix_socket_*` externs
  per D-4 signatures. Wire into the runtime's extern table.
- `src/lib/nogc_sync_mut/service/` (new directory):
  - `mod.spl`, `daemon_base.spl`, `pid_file.spl`, `uds_server.spl`,
    `request_loop.spl`, `request_queue.spl` (FIFO + priority lanes),
    `lease_manager.spl`, `audit_log.spl`, `signal_handlers.spl` (reuse
    `src/lib/nogc_sync_mut/signal_handlers.spl` if compatible).
- After externs land: run `scripts/bootstrap/bootstrap-from-scratch.sh
  --deploy` (D-4 / `feedback_extern_bootstrap_rebuild.md`).
- Make Phase-4 service-base specs **green**.

### I-B — `simple_vcs_daemon` (depends on I-A)

**Scope:**
- `src/app/sj_daemon/` (new): `main.spl`, `daemon.spl`, `jj_exec.spl`
  (read-bypass-lane constant + injection per D-2), `git_mimic.spl`
  (R-D translation table), `forbidden.spl` (D-1 + 4 other
  forbidden verbs), `submodule_policy.spl` (D-8), `ghost_index_lock.spl`
  (D-6), `stash_stack.spl` (D-11).
- ECS components/systems live here per the table in `state.md`
  lines 594–617.
- Make Phase-4 daemon specs **green**.

### I-C — `bin/sj` client (parallel-safe with I-A/I-B; coordinates via UDS contract)

**Scope:**
- `src/app/sj/` (new): `main.spl`, `cli.spl` (parser for the grammar in
  `state.md` lines 810–826), `client.spl` (UDS client → `simple_vcs_daemon`),
  `fallback.spl` (in-process call when daemon not running), `bus_mode.spl`
  (BUSY backoff with jitter — read D-5 contract).
- `bin/sj.cmd` wrapper (per R-B's MCP wrapper convention; default = run
  `.spl`; gate cache behind `SIMPLE_SJ_USE_CACHE=1` per
  `feedback_mcp_cache_off_by_default.md`).
- Make Phase-4 CLI specs **green**.

### I-D — migration sweep (last; depends on I-A/B/C compiling)

**Scope (from R-C's classification in `state.md` lines 941–995):**
- `migrate-now` (9 items): `sync.spl`, `main_lazy_vcs_tools.spl`,
  `vcs_collector.spl`, `jj_app.spl`, help strings — straight rewrite to
  `sj` calls.
- `migrate-with-care` (4 items): `jj_runner.spl` (the central
  chokepoint — verify exit-code contract), `tools_jj_git.spl`,
  `commit.spl`, the release-doc mixed pattern.
- `keep-raw` (9 items): external-repo scripts, git hooks, the new
  daemon/client themselves. Add comments explaining why.
- `doc-only` (~10 `.md` files): `CLAUDE.md`, `.claude/rules/vcs.md`,
  agent/skill docs, `doc/07_guide/quick_reference/sj_cli.md` (new shim doc
  per AC-5).
- `bin/sj` symlink wiring in `scripts/setup.sh`.

---

## 8. Phase 6/7/8 — short recipes

**6 — refactor:** spawn 1 agent with `/simplify` skill; targets:
- collapse duplication between `sj` client (I-C) and daemon's in-process
  fallback path (I-C `fallback.spl`)
- collapse duplication in the git-mimic translator (I-B `git_mimic.spl`)
  if R-D's table-driven approach landed as N hand-written handlers

**7 — verify:** spawn 1 agent with `/verify`. Run:
- `bin/simple test` (full)
- the new concurrency smoke + ghost-lock smoke + stash-persistence smoke
- a parallel-claudes simulation: 2 clients hammering the daemon while a
  3rd reads, plus `sync.spl` exercising the BUSY contract
- AC-1..AC-7 sign-off table appended to `state.md` `### 7-verify`

**8 — ship:** spawn 1 agent with `/sync`. Rules from memory:
- **Per-phase commits** as we go — no chore: sync bundling
  (`feedback_sync_bundling_clobbers_commits.md`)
- If jj is contended: push via detached worktree
  (`feedback_push_via_worktree.md`)
- Verify `git log` after push
  (`feedback_force_push_kernel_arc.md`)
- Pause other parallel `/dev` runs first
  (`feedback_submodule_race_parallel_dev.md`)
- Don't commit Phase-3 design doc until Phase-5 starts; commit
  `state.md` only after Phase-8 completes (it is a working artifact)

---

## 9. Files this feature has produced so far

| Path | Lines | Status | Purpose |
|------|-------|--------|---------|
| `.sstack/jj-wrapper-daemon/state.md` | 1041 | untracked | SStack state file — single source of truth |
| `.sstack/jj-wrapper-daemon/RESUME_PLAN.md` | (this) | untracked | Restart guide |
| `doc/04_architecture/sj_vcs_service.md` | 431 | untracked | Durable design doc |

**Not yet touched** (Phase 5 will create these):
- `src/runtime/uds.rs`
- `src/lib/nogc_sync_mut/service/**`
- `src/app/sj/**`
- `src/app/sj_daemon/**`
- `bin/sj`, `bin/sj.cmd`
- `test/unit/lib/service/**`, `test/unit/app/sj/**`, `test/system/sj_*_spec.spl`
- `doc/07_guide/quick_reference/sj_cli.md`

---

## 10. TaskList state at pause

```
#1. [completed] SStack Phase 1 — dev (refine goal & ACs)
#2. [completed] SStack Phase 2 — research (4 parallel sub-agents)
#3. [in_progress] SStack Phase 3 — arch (design service base + sj daemon)
#4. [pending] SStack Phase 4 — spec (BDD specs)
#5. [pending] SStack Phase 5 — implement (4 parallel engineers)
#6. [pending] SStack Phase 6 — refactor (/simplify pass)
#7. [pending] SStack Phase 7 — verify (full QA gate)
#8. [pending] SStack Phase 8 — ship (per-phase commits + push)
```

**On restart:** mark #3 completed (Phase 3 is fully written; the `[in_progress]`
marker is only because the user paused before the orchestrator clicked it
done), then set #4 to in_progress.

---

## 11e. ⚠️ CRITICAL — Untracked work disappeared during session (2026-04-26)

**Symptom (verified at session end via `ls` + `git status`):**

GONE from disk (but state.md + RESUME_PLAN.md SURVIVED):
- `doc/04_architecture/sj_vcs_service.md` — Phase-3 design doc (431 lines)
- `doc/04_architecture/sj_mdsoc_plus_template.md` — Phase-4 MDSOC+ template
- Entire `src/lib/nogc_sync_mut/service/` directory (11 .spl files, ~21 KB)
- `test/unit/runtime/uds_extern_spec.spl`
- Entire `test/unit/lib/service/` directory (multiple specs)
- Entire `test/unit/app/sj/` directory (multiple specs)
- `test/system/sj_concurrency_spec.spl`, `sj_ghost_index_lock_spec.spl`,
  `sj_push_pattern_spec.spl`

SURVIVED:
- `.sstack/jj-wrapper-daemon/state.md` (86 KB) and this file
- `src/compiler_rust/runtime/src/value/net_uds.rs` (11 KB, my new Rust externs)
- `src/compiler_rust/compiler/src/interpreter_extern/qmp_socket.rs` (with server handlers appended)
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` (with dispatch entries)

**Likely cause:** parallel claude session in another terminal ran `git
clean -fd` or similar. Evidence:
- `git status` shows NEW modifications I did not make in this session:
  `.claude/agents/sstack/ship.md`, `src/app/itf/{config,main}.spl`,
  `src/os/apps/sshd/{ssh_cipher,ssh_kex,ssh_session,ssh_transport}.spl`,
  newly added `test/unit/os/apps/sshd/ssh_session_kex_spec.spl` (mode `A `)
- `jj op log` only shows statusline-driven `snapshot working copy` ops —
  no `abandon` or destructive op visible there, but `git clean` happens
  outside jj's op log
- Survival pattern: anything I had **modified** an existing file (M
  status) survived; everything **newly added** (?? untracked + new dirs)
  was wiped — exactly the pattern of `git clean -fd` (deletes untracked).
- Memory entries that warned about this: `feedback_submodule_race_parallel_dev.md`,
  `feedback_destructive_upstream_detection.md`,
  `feedback_hosted_parity_scope.md`.

**Recovery options (pick before continuing):**

1. **`jj op log` deeper inspection** — the lost files were committed by
   jj's auto-snapshot at various points; an earlier op may still hold
   them. Try `jj op log --no-pager --limit 50` and look for ops between
   2026-04-26 04:30 and 05:30 with file additions to `service/` or
   `test/unit/lib/service/`. If found: `jj op restore <op-id>` will roll
   the working copy back, but it will also revert the legitimate non-feature
   changes from the parallel claude.
2. **`.git/lost-found` / git fsck --dangling** — `git clean` does not
   delete from the object store immediately; if the files were ever
   staged or auto-snapshotted into a jj commit, the blobs may still be
   recoverable via `git fsck --dangling` + `git cat-file`. High effort,
   medium success.
3. **Rebuild from this session's state.md** — `state.md` (86 KB)
   contains the full Phase-2/3/4 content inline, including:
   - Phase-3 architecture summary (`### 3-arch` section, lines ~403–617):
     module plan, dependency map, 11 ADRs, public API signatures, MDSOC+
     capsule diagram, ECS table
   - Phase-2 R-D translation table and decisions
   - Detailed design rationale for every D-1..D-11
   The design doc and MDSOC+ template can be regenerated from these
   sections. Spec files can be regenerated from the §6 Phase-4 recipe.
   Service base .spl files would need to be rebuilt from scratch — they
   were never captured in state.md, only their file list.

**Recommended:** option 1 (jj op restore) if the working copy from the
parallel claude can be tolerated; option 3 (rebuild from state.md) if
not. Either way: **before any further Phase-5 work, coordinate with the
parallel claude session** to prevent another wipe (per
`feedback_submodule_race_parallel_dev.md` — "pause parallel tracks first").

**Update (2026-04-26, end of late session) — recovery probe results:**

Tried `jj diff --from c0144117a353 --to @ --summary` and discovered:
- Op c0144117a353 corresponds to change-id `quvtswurwknommstxnwluklppnzrpmkq`
  (commit `a7e946ce1b554254a267034410ed7b48aaa3f144`)
- Diff against @ is only 4 lines — **the lost files do NOT appear in this diff**,
  meaning c0144117a353 was already POST-destruction
- The files vanished at an op older than c0144117a353

Need to scan further back. **BUT** during the second probe attempt,
`.git/index.lock` was actively held by the parallel claude session and
every subsequent `jj` command failed:

```
Error: Failed to reset Git HEAD state
Caused by:
1: Could not acquire lock for index file
2: The lock for resource '/home/ormastes/dev/pub/simple/.git/index' could
   not be obtained immediately after 1 attempt(s). The lockfile at
   '/home/ormastes/dev/pub/simple/.git/index.lock' might need manual
   deletion.
```

**This is exactly the failure mode the sj VCS daemon is designed to
prevent.** The recovery is currently blocked by the same problem.

**Final restart procedure:**
1. **Identify and pause the parallel claude session** — check for running
   claude processes (`ps aux | grep claude`), or check other terminal
   windows. Pause or kill it. Do NOT proceed until the repo is quiet.
2. **Verify `.git/index.lock` is gone** — `ls -la .git/index.lock`. If it
   still exists with no live holder, `rm .git/index.lock`.
3. **Open a fresh claude session** (not this one — context exhausted).
4. **In the fresh session, scan jj op log far enough back** to find the
   op where the lost files still existed:
   ```bash
   jj op log --no-pager --limit 200
   # Look for ops around 04:30-05:00 timestamp range; ops where args
   # mention spawning sub-agents or doing service/ work
   ```
5. **Probe candidate ops with `jj diff --from <op-change-id> --to @ --summary`**
   to find one whose diff includes the lost paths (will appear as
   D rows for `src/lib/nogc_sync_mut/service/...`,
   `doc/04_architecture/sj_vcs_service.md`, `test/unit/runtime/uds_extern_spec.spl`,
   etc.). To get the change-id at op X, use:
   `jj log -r @ --no-graph --at-op <op-X> -T 'change_id ++ "\n"'`
6. **Restore the files surgically with `jj restore --from <change-id> <paths>`** —
   keeps everything else intact (Rust externs and parallel claude's work).

If step 4-6 doesn't find the files, fall back to **rebuild from state.md**
(option 3 in the original list) — the design content is preserved inline.

**Confirmed root cause (jj op log inspection, 2026-04-26):**

```
○    f7660d8a085d ormastes@dl 5 minutes ago, lasted 5 milliseconds
├─╮  reconcile divergent operations           ← this is where files vanished
│ │  args: jj git push --bookmark main         ← parallel claude pushed
○ │    91a9484011cd ormastes@dl 5 minutes ago, lasted 5 milliseconds
├───╮  reconcile divergent operations
○ │ │  e5f66ec3d662 ormastes@dl 5 minutes ago
│ │ │  point bookmark main to commit 20ea5265ab5e9e3532c18c26a226b6d87ba48aeb
│ │ │  args: jj bookmark set main -r 20ea5265ab5e --allow-backwards
○  c0144117a353 ormastes@dl 5 minutes ago      ← LIKELY HAS THE LOST FILES
│  snapshot working copy
```

The parallel claude pushed `main` to a different commit (`20ea5265…`) and
the divergent-op reconcile collapsed away my working-copy state.

**Concrete recovery recipe (run in a FRESH session after coordinating
with the parallel claude — don't run from this stuck session):**

```bash
# 1. Confirm c0144117a353 has the lost files
jj diff --from c0144117a353 --to @ --summary | head -40
# Look for D rows (deletions) for service/, sj_vcs_service.md, sj_mdsoc_plus_template.md, sj_*_spec.spl

# 2. SAFEST: restore only the missing paths, not the whole working copy
#    (preserves my Rust externs and the parallel claude's legitimate work)
jj restore --from c0144117a353 \
  doc/04_architecture/sj_vcs_service.md \
  doc/04_architecture/sj_mdsoc_plus_template.md \
  src/lib/nogc_sync_mut/service/ \
  test/unit/runtime/uds_extern_spec.spl \
  test/unit/lib/service/ \
  test/unit/app/sj/ \
  test/system/sj_concurrency_spec.spl \
  test/system/sj_ghost_index_lock_spec.spl \
  test/system/sj_push_pattern_spec.spl

# 3. Verify recovery
ls src/lib/nogc_sync_mut/service/
ls test/unit/runtime/uds_extern_spec.spl
ls doc/04_architecture/sj_*.md

# 4. Then run the smoke spec
bin/simple test test/unit/runtime/uds_extern_spec.spl
```

**Fallback if `jj restore --from` syntax differs in this jj version
(check with `jj restore --help`):**

```bash
# Roll the WHOLE working copy back to before the reconcile (destructive
# to parallel claude's work — coordinate first!)
jj op restore c0144117a353

# Then cherry-pick my Rust externs back forward (their content is in
# state.md / RESUME_PLAN.md). The 3 files to restore manually:
#   - src/compiler_rust/runtime/src/value/net_uds.rs (new, ~180 lines)
#   - src/compiler_rust/runtime/src/value/net.rs (added 2 use lines + 1 include!)
#   - src/compiler_rust/compiler/src/interpreter_extern/qmp_socket.rs (appended 5 fns + LISTENERS)
#   - src/compiler_rust/compiler/src/interpreter_extern/mod.rs (added 5 dispatch lines after line 846)
```

**My Rust extern work this turn (still good and ready to use):**
- `src/compiler_rust/runtime/src/value/net_uds.rs` — 6 externs, compiled clean (`cargo check -p simple-runtime` 3.99s)
- `src/compiler_rust/compiler/src/interpreter_extern/qmp_socket.rs` — 5 server handlers + LISTENERS registry
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — 5 dispatch entries (lines 847–851)
- `cargo check -p simple-compiler` clean (17.51s)
- Driver release build clean (1m 36s)
- Spec smoke could not run because `uds_extern_spec.spl` was wiped. Once
  recovered/rebuilt, run: `bin/simple test test/unit/runtime/uds_extern_spec.spl`

---

## 11d. Phase 5 — UDS externs landed inline (2026-04-26, late session)

After three sub-agent stalls (I-A: 79 tools, I-A.1: 8 tools, Codex rescue:
1 tool), the orchestrator wrote the externs directly. **`cargo check -p
simple-runtime` is clean.**

**Files written:**
- `src/compiler_rust/runtime/src/value/net_uds.rs` — 6 externs (5 server
  + bonus `rt_unix_socket_connect` client extern that was missing)
- `src/compiler_rust/runtime/src/value/net.rs` — added 2 `use` statements
  + `include!("net_uds.rs")`

**You (user) need to run these next, in order:**

```bash
# 1. Bootstrap deploy (5-15 min) — MANDATORY after rt_* extern additions
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# 2. Run the smoke spec
bin/simple test test/unit/runtime/uds_extern_spec.spl
```

**Known issue to fix before I-B can start:** `rt_unix_socket_recv` Rust
signature is `recv(fd, max_len, *mut out_len) -> ptr` but `service/extern.spl`
declares it as `recv(fd, max_len) -> [u8]`. The mismatch means I-B's request
loop won't work until reconciled. **Recommended fix:** rewrite the Rust
`rt_unix_socket_recv` to allocate via the runtime's `[u8]` allocator (look at
how `rt_fd_read_until` returns text — same pattern). State file `### 5-implement
/ #### I-A.2` has the full TODO list including this.

---

## 11c. Phase 5 stalled — exact restart path (2026-04-26, late session)

**Symptom:** I-A sub-agent ran 24min/79 tools, stopped without final output.
I-A.1 narrow-scope retry ran 41s/8 tools, stopped without final output.
Both produced partial work but neither wrote the state-file summary or
finished the critical externs. Pattern is consistent → likely sub-agent
budget/timeout, not the prompts.

**The blocker that's actually one focused hour of work:**

Phase 5 is gated on writing 5 UDS server-side externs in Rust. The previous
agents wasted time searching for the right files. Here are the exact paths
already located (orchestrator session, 2026-04-26 late):

- **Existing UDS client extern lives in:**
  `src/lib/nogc_sync_mut/qemu/qmp_client.spl:14`
  declares `rt_unix_socket_connect(path: text) -> i64`
- **Rust runtime FFI directory:**
  `src/compiler_rust/runtime/src/value/ffi/`
- **Existing networking Rust impl:**
  `src/compiler_rust/runtime/src/value/net.rs` (TCP+UDP+probably UDS client)
  Sister files: `net_tcp.rs`, `net_udp.rs`, `monoio_future.rs`
- **Extern registration site:** look in `value/ffi/` (mod.rs) and
  `value/mod.rs` — they reference `file_ops.rs` and similar; the registration
  pattern there shows where the dispatcher table lives. `rt_getpid` lives in
  `src/compiler_rust/runtime/src/value/ffi/file_io/` per grep.

**The 5 externs needed (signatures locked in `src/lib/nogc_sync_mut/service/extern.spl`):**
```
rt_unix_socket_listen(path: text, backlog: i32) -> i64
rt_unix_socket_accept(fd: i64) -> i64
rt_unix_socket_send(fd: i64, data: [u8]) -> i64
rt_unix_socket_recv(fd: i64, max_len: i64) -> [u8]
rt_unix_socket_close(fd: i64) -> i32
```

**Restart recipe (Option 4 — one-pass focused script, ~60–90 min):**

> You are SStack Phase-5 sub-agent **I-A.2** — final completion of I-A.
> Do EXACTLY these steps and STOP:
>
> 1. **Read** `src/compiler_rust/runtime/src/value/net.rs` end-to-end and
>    locate `rt_unix_socket_connect` impl (it implements the connect-side
>    extern declared at `src/lib/nogc_sync_mut/qemu/qmp_client.spl:14`).
> 2. **Read** the file's mod.rs sibling and `value/ffi/mod.rs` to learn
>    the extern registration pattern (where `rt_unix_socket_connect` is
>    registered with the dispatcher).
> 3. **Add 5 server-side externs** following the same pattern as the
>    connect impl. Use `std::os::unix::net::UnixListener`/`UnixStream`.
>    Make `accept` non-blocking (set `set_nonblocking(true)` on the
>    listener; return `-EAGAIN` (-11) when no pending connection).
>    Match signatures EXACTLY as declared in
>    `src/lib/nogc_sync_mut/service/extern.spl`.
> 4. **Register** the 5 functions in the dispatcher table next to
>    `rt_unix_socket_connect`.
> 5. **Build the runtime:** `cargo build --release --manifest-path
>    src/compiler_rust/runtime/Cargo.toml` (or whatever the project's
>    cargo invocation is — read `scripts/bootstrap/bootstrap-from-scratch.sh`
>    for the right path).
> 6. **Run bootstrap deploy:**
>    `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`
>    (NOT `bin/simple build bootstrap` — wrapper whitelist no-ops it).
> 7. **Run the spec smoke** for just the extern test:
>    `bin/simple test test/unit/runtime/uds_extern_spec.spl`
>    (interpreter mode; do NOT use `--mode=native`/`--mode=smf`).
> 8. **Append `#### I-A.2` to `state.md` `### 5-implement`** with:
>    - Exact files modified
>    - Bootstrap-deploy log tail (last 20 lines)
>    - Spec result for `uds_extern_spec.spl`
>    - One paragraph for I-B telling them the public service API is
>      ready (`use std.service.{...}`)
> 9. **STOP.** Do not run other specs. Do not touch other files. Do not
>    expand scope.
>
> Tools: Bash, Read, Write, Edit, ctx-mode (`mcp__plugin_context-mode_context-mode__ctx_*`).
> Do NOT call advisor() — it eats time and this is mechanical.
> Hard stop at 90 minutes.

**Alternative (Option 5 — human writes the externs):**

Three Rust files to touch (paths confirmed by orchestrator):
1. Open `src/compiler_rust/runtime/src/value/net.rs` — copy the
   `rt_unix_socket_connect` impl pattern, write 5 server-side functions.
2. Open the dispatcher mod.rs (find via `grep -l rt_unix_socket_connect
   src/compiler_rust/runtime/src/value/`) and add 5 `register!()` lines.
3. Run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` then
   `bin/simple test test/unit/runtime/uds_extern_spec.spl`.

Estimated 60-90 minutes of focused work.

---

## 11b. Phase 5 I-A partial completion (2026-04-26)

I-A sub-agent ran 24 minutes / 79 tool uses, then stopped without writing a
final summary. State of the world right now:

**What landed:**
- `src/lib/nogc_sync_mut/service/` — 11 .spl files (mod, extern, daemon_base,
  lifecycle, uds_server, request_loop, request_queue, lease_manager,
  audit_log, signal_handlers, traits). Total ~21 KB. Probably compiles
  in isolation but NOT verified.
- `doc/04_architecture/sj_mdsoc_plus_template.md` (from Phase 4)
- All 17 Phase-4 spec files (no changes by I-A — the agent was about to
  fix import paths from `app.sj_daemon.X` → `std.service.X` but unclear
  whether that landed)

**What's missing (BLOCKER for I-B/I-C):**
- **`src/runtime/uds.rs`** — Rust impl of 5 UDS externs. Without these,
  `service/extern.spl` declarations dangle.
- Bootstrap rebuild — `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`
  not run.
- Spec smoke results — none captured.
- Verification that I-A's spec-import-path fix actually landed.

**Naming divergence to resolve:**
- I-A produced `lifecycle.spl` instead of design's `pid_file.spl`.
  Options: (a) keep `lifecycle.spl` (broader concern, fine), (b) rename
  to match design. Either is acceptable; just be consistent in
  cross-references.

**Restart recipe (Option 2 — narrow-scope I-A.1):**

> You are SStack Phase-5 sub-agent **I-A.1** — narrow-scope completion
> of I-A. Read `.sstack/jj-wrapper-daemon/RESUME_PLAN.md` §11b and
> `state.md` § "I-A — service base library (PARTIAL)". Your scope is
> exactly: (1) write `src/runtime/uds.rs` implementing the 5 UDS server
> externs per signatures in `src/lib/nogc_sync_mut/service/extern.spl`;
> (2) register them in the runtime extern dispatch table (search for
> `rt_unix_socket_connect` to find the registration site); (3) run
> `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`; (4) verify
> Phase-4 spec import paths use `std.service.X` not `app.sj_daemon.X`
> and fix any that drifted; (5) run the 7 service-base specs in
> interpreter mode and capture pass/fail; (6) append `#### I-A.1` to
> `state.md ### 5-implement` with file list, bootstrap log tail, and
> spec-result table. Do NOT touch `src/app/sj/`, `src/app/sj_daemon/`,
> migration sweep, or anything else outside the runtime extern + spec
> verification scope. Call advisor() once after extern impl, before
> bootstrap. Hard stop after 60 minutes — write a BLOCKED section if
> you can't finish.

---

## 11a. Advisor sanity-check on Phase-3 (2026-04-26, post-restart)

Called `advisor()` on Phase-3 design before launching Phase 4. Two blockers,
four recipe adjustments, one housekeeping note. **Two blockers must be
resolved with the user before Phase-4 specs are written.**

**RESOLVED 2026-04-26 (user "continue"):**
- D-1 → **(a) Forbid** stays. Architect's call stands.
- D-11 → **dropped from v1**. `sj git stash` returns `FORBIDDEN` with the
  message "use `jj new -m wip-<topic>` instead — jj's working-copy-as-commit
  makes stash unnecessary". Phase-4 must NOT spec stash; Phase-5 I-B must
  NOT implement `stash_stack.spl` or `.sj/stash_stack.json`.

**Blocker A — D-1 (`git rebase -i` → FORBIDDEN) needs user OK.**
The user's pasted reference table explicitly mapped `git rebase -i → jj arrange`.
R-A found `jj arrange` doesn't exist in jj 0.32.0. The architect picked
"forbid" unilaterally — but the user named this verb in the request, so the
call belongs back with the user. Three live alternatives:
- (a) **Forbid** with educational error (current D-1).
- (b) **Raw passthrough** to `git rebase -i` — daemon serializes, jj
  re-snapshots after.
- (c) **Compose** `jj rebase` + `jj split`/`jj squash` for the common cases
  (reorder, edit, drop). Drop the interactive editor; expose a small
  scriptable surface instead.

→ **Awaiting user decision before Phase-4 spec writes the assertion.**

**Blocker B — D-11 (stash stack) is scope creep, drop for v1.**
User's 4-item request didn't mention stash. R-D added it speculatively;
D-11 turned it into a persistent JSON stack across daemon restarts — its own
state machine. Defer to a follow-up. Phase-4 should NOT spec it; Phase-5 I-B
should NOT implement it.

→ **Default action: drop D-11 from v1. User can override.**

**Phase-4 recipe adjustments (apply when restarting Phase 4):**
1. **Lead with a UDS-extern smoke** before service-base integration: a
   30-line standalone roundtrip in `test/unit/runtime/uds_extern_spec.spl`
   that exercises the 5 new `rt_unix_socket_*` externs end-to-end. Run
   before I-A starts on the service base. Cheap, decisive.
2. **Drop full table-driven translation spec** (~50 verbs). One spec per
   category (direct-jj, multi-step, raw-passthrough, forbidden) + one
   regression case ≈ 6 spec files. Full-table coverage moves to Phase-7
   verify. Fewer specs = fewer interpreter-weirdness surfaces.
3. **Spec writer must define "MDSOC+ compliant" concretely** for I-A/B/C:
   one-page sub-doc describing file layout, naming, allowed imports between
   the outer capsule and inner ECS layers. R-B found zero `@capsule`
   annotations in tree, so the four parallel engineers will be inventing
   the pattern — give them the same template.
4. **Drop the in-prompt `advisor()` nudge for Phase-4 sub-agent.** Save
   advisor calls for Phase-5 implementers where it earns its keep.

**Pre-Phase-7 housekeeping:**
- Manually clear the 6.6 MB ghost `.git/index.lock` once jj is quiet.
  D-6's reclaim rule should be exercised by **test-staged** ghost locks
  with controlled inputs; mixing real and staged pollutes the test signal.

**Confirmed sound (no action needed):**
- MDSOC+ as architectural constraint
- D-4 extern signatures (smoke-first addresses the risk)
- D-5 BUSY exit-code 75 + `ERROR[BUSY]:` prefix
- D-6 three-AND ghost-lock reclaim rule
- D-8 submodule auto-pin (directly responsive to user's documented pain)

---

## 11. Open issues parked at pause (do not lose)

1. **Stale 6.6 MB `.git/index.lock` in this repo** (R-A finding) — currently
   blocks some `jj op log` calls. Decide pre-Phase-7 whether to clear
   manually or use as a live test of D-6's reclaim rule.
2. **Advisor sanity-check on Phase-3 design** — the orchestrator was about to
   call `advisor()` with the full Phase-3 design before launching Phase-4.
   This is still recommended; the user paused before it ran. Do it on
   restart unless the user says skip.
3. **`jj` version pinning** — local jj is 0.32.0 (R-A). The design assumes
   this. If a future jj release ships `jj arrange`, revisit D-1.
4. **74 unrelated uncommitted changes** in the repo at pause (B4-sugar WIP,
   bignum, BDD runtime, ssh, etc) — none touch this feature's scope, but
   they may interleave with the sstack work during Phase-8. Coordinate
   with whoever is driving those branches before shipping.

---

## 12. Pointer index

- **State file:** `.sstack/jj-wrapper-daemon/state.md`
- **Design doc:** `doc/04_architecture/sj_vcs_service.md`
- **MDSOC+ reference:** `doc/04_architecture/mdsoc_architecture_tobe.md`
- **Memory dir (user):** `/home/ormastes/.claude/projects/-home-ormastes-dev-pub-simple/memory/`
- **Pipeline definitions:** `.claude/skills/lib/sstack_phases.md`
- **Agent role defs:** `.claude/agents/sstack/{dev,research,arch,spec,implement,refactor,verify,ship}.md`
- **Project rules:** `.claude/rules/{language,testing,bootstrap,commands,structure,code-style,vcs}.md`
- **Critical memory entries this feature must respect:**
  - `feedback_mdsoc_plus_default.md`
  - `feedback_extern_bootstrap_rebuild.md`
  - `feedback_compile_mode_false_greens.md`
  - `feedback_class_trait_header_form_also_fails.md`
  - `feedback_test_imports.md`
  - `feedback_interpreter_test_limits.md`
  - `feedback_push_via_worktree.md`
  - `feedback_jj_submodule_gitlinks.md`
  - `feedback_submodule_race_parallel_dev.md`
  - `feedback_sync_bundling_clobbers_commits.md`
  - `feedback_parallel_sonnet.md`
  - `feedback_parallel_scope_partition.md`
  - `feedback_subagent_advisor_access.md`
  - `feedback_mcp_cache_off_by_default.md`

— end of resume plan —
