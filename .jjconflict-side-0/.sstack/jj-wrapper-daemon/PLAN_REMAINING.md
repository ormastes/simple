# Remaining Work Plan — `jj-wrapper-daemon` (sj VCS service)

> **Forward-looking plan doc.** What's done is in `state.md`. History/context
> in `RESUME_PLAN.md`. This file is just what still needs doing, in order,
> with concrete recipes.
>
> **Last updated:** 2026-04-26 (end of session that completed Phase-5 / I-A)
> **Branch:** `main` (per `.claude/rules/vcs.md` — never branch)

---

## 0. Status snapshot

| Phase | Status | Notes |
|-------|--------|-------|
| 1 — dev | ✅ done | Refined goal + 7 ACs in state.md L32–73 |
| 2 — research | ✅ done | R-A/B/C/D parallel; outputs in state.md |
| 3 — arch | ✅ done | 11 ADRs + MDSOC+ capsule + ECS table; design doc at `doc/04_architecture/sj_vcs_service.md` |
| 3.5 — advisor sanity-check | ✅ done | D-1 forbid stays; D-11 stash dropped |
| 4 — spec | ✅ done | 17 specs + MDSOC+ template at `doc/04_architecture/sj_mdsoc_plus_template.md` |
| 5 — implement | ⏳ in progress | **I-A done (5/5 green)**; I-B/I-C/I-D remaining |
| 6 — refactor | ⏸ pending | `/simplify` pass after Phase 5 |
| 7 — verify | ⏸ pending | Full QA gate; needs bootstrap deploy |
| 8 — ship | ⏸ pending | Per-phase commits, push via worktree if jj contended |

---

## 1. Pre-checkpoint: commit what's working NOW

Before starting I-B, commit the I-A checkpoint per
`feedback_sync_bundling_clobbers_commits.md` (per-phase, not bundled). The
modified/added files specifically attributable to the sj feature:

```bash
# Sanity diff first (always)
jj diff --summary | grep -E "(sj_|service/|net_uds|qmp_socket|interpreter_extern/mod|uds_extern_spec)"

# Stage just sj-feature paths (avoid bundling the parallel claude's
# unrelated work — see RESUME_PLAN.md §11e)
jj commit \
  src/compiler_rust/runtime/src/value/net_uds.rs \
  src/compiler_rust/runtime/src/value/net.rs \
  src/compiler_rust/compiler/src/interpreter_extern/qmp_socket.rs \
  src/compiler_rust/compiler/src/interpreter_extern/mod.rs \
  src/lib/nogc_sync_mut/service/ \
  doc/04_architecture/sj_vcs_service.md \
  doc/04_architecture/sj_mdsoc_plus_template.md \
  test/unit/runtime/uds_extern_spec.spl \
  test/unit/lib/service/ \
  test/unit/app/sj/ \
  test/system/sj_concurrency_spec.spl \
  test/system/sj_ghost_index_lock_spec.spl \
  test/system/sj_push_pattern_spec.spl \
  .sstack/jj-wrapper-daemon/ \
  -m 'feat(sj): Phase 5 I-A — std.service base + 5 UDS externs (5/5 smoke green)

- Rust runtime FFI: rt_unix_socket_{listen,accept,send,recv,close} + connect
  in src/compiler_rust/runtime/src/value/net_uds.rs (wired via include!)
- Interpreter dispatch: 5 server handlers in qmp_socket.rs + dispatch entries
  in interpreter_extern/mod.rs (lines 847–851)
- Service base library: 11 .spl files in src/lib/nogc_sync_mut/service/
  (MDSOC+ outer + ECS-ready scaffolding for I-B)
- Phase-3/4 design docs (sj_vcs_service.md 431 lines, sj_mdsoc_plus_template.md 209 lines)
- 17 Phase-4 BDD specs (1 green, 16 awaiting I-B/I-C/I-D)
- uds_extern_spec.spl: 5 examples, 0 failures (200 ms) end-to-end
'

# Push (jj-colocated)
jj bookmark set main -r @-
jj git push --bookmark main
```

**If `.git/index.lock` contention from a parallel claude:** use
`feedback_push_via_worktree.md`'s detached-worktree path. Memory has the
exact commands.

---

## 2. I-B — `simple_vcs_daemon` (next; gates I-C/I-D)

**Estimated:** 4–8 hours. Must be one focused session. Not splittable into
parallel sub-agents (single MDSOC+ daemon, single dependency tree).

**Scope (`src/app/sj_daemon/`, all new):**
- `main.spl` — entrypoint; wires daemon_base → request handler → SIGTERM
- `daemon.spl` — top-level capsule; instantiates the request loop
- `jj_exec.spl` — wraps shellout to `jj` binary; injects
  `--ignore-working-copy --no-pager --color never` on every read-bypass-lane
  verb (canonical list per D-2 / state.md)
- `git_mimic.spl` — table-driven git→jj translator. Use R-D's table in
  state.md L649–733 as the source of truth.
- `forbidden.spl` — D-1 (`rebase -i` forbidden) + 4 other forbidden verbs
  (`push --force`, bare `push`, bare `checkout`, `filter-branch`). Each
  returns `ERROR[FORBIDDEN]: <message>` with the exact strings from R-D L752.
- `submodule_policy.spl` — D-8 accept-with-warn + auto-pin via raw
  `git commit --no-verify` inside the exclusive lease window.
- `ghost_index_lock.spl` — D-6 three-AND rule (lsof empty AND mtime>30s
  AND no live daemon lease references git). Scans
  `.git/worktrees/*/index.lock` too.
- `request_handler.spl` — implements the `RequestHandler` trait from
  `std.service.traits`. This is the API surface I-C calls into.
- `extern.spl` — local re-declarations of any externs used (mostly just
  re-exports from `std.service.extern`)

**ECS components/systems** (per state.md L594–617): live in their own
files under `src/app/sj_daemon/ecs/`:
- `request_component.spl` — Request entity + components
  (`Lane`, `Verb`, `Args`, `LeaseTtl`, `IssuedAt`)
- `lease_component.spl` — Lease entity + components
  (`HolderPid`, `Class`, `Granted`, `Expires`)
- `operation_component.spl` — Operation entity (in-flight child process
  + audit-log refs)
- `systems.spl` — the systems that advance entities each tick (queue
  drain, lease grant, watchdog, audit append)

**Constraints:**
- **MDSOC+** — outer capsules in `src/app/sj_daemon/`; ECS in
  `src/app/sj_daemon/ecs/`. Capsules import ECS systems, not the other
  way around. Reference: `doc/04_architecture/sj_mdsoc_plus_template.md`.
- **No header-form trait conformance** — always
  `impl RequestHandler for X { … }` blocks (per
  `feedback_class_trait_header_form_also_fails.md`).
- **No inheritance, generics with `<>` not `[]`** (per
  `.claude/rules/language.md`).
- **`use std.io_runtime`**, never `app.io` (per
  `feedback_test_imports.md`).
- **NEVER convert TODO/FIXME to NOTE** — implement or delete.

**Spec gate (must go green before I-B is "done"):**
```bash
bin/simple test test/unit/lib/service/lease_grant_spec.spl
bin/simple test test/unit/lib/service/lease_ghost_reclaim_spec.spl
bin/simple test test/unit/lib/service/lease_max_hold_spec.spl
bin/simple test test/unit/lib/service/service_lifecycle_spec.spl
bin/simple test test/unit/lib/service/uds_server_spec.spl
bin/simple test test/unit/lib/service/request_queue_spec.spl
bin/simple test test/unit/app/sj/forbidden_verbs_spec.spl
bin/simple test test/unit/app/sj/submodule_policy_spec.spl
bin/simple test test/unit/app/sj/ignore_working_copy_spec.spl
```

Some specs may need import-path reroutes similar to `uds_extern_spec.spl`
(originally specced against `app.sj_daemon.X` modules that I-B is now
creating).

**Sub-agent recipe (give to a fresh general-purpose Sonnet agent):**

> You are SStack Phase-5 sub-agent **I-B** for `jj-wrapper-daemon`.
> Read `.sstack/jj-wrapper-daemon/state.md`,
> `.sstack/jj-wrapper-daemon/PLAN_REMAINING.md` §2,
> `doc/04_architecture/sj_vcs_service.md`,
> `doc/04_architecture/sj_mdsoc_plus_template.md`. I-A.4 already shipped
> the service base + UDS externs (5/5 smoke green). Your scope is exactly
> the file list under "Scope" in §2. Make the spec gate (9 specs) go
> green. Do NOT touch `src/app/sj/`, migration targets, or
> `src/lib/nogc_sync_mut/service/`. Hard stop after 6 hours; if blocked,
> append `#### I-B BLOCKED` to state.md `### 5-implement` with the
> failing spec output and what you tried. Call `advisor()` once after
> the request-handler trait impl is sketched but before the lease state
> machine, to sanity-check capsule boundaries.

---

## 3. I-C — `bin/sj` client (parallel with I-B once trait is stable)

**Estimated:** 2–4 hours. Can fan out parallel with I-B once I-B's
`RequestHandler` trait is stable in `std.service.traits` (likely after
I-B's first 30 min of work).

**Scope (`src/app/sj/`, all new):**
- `main.spl` — entrypoint; argv parsing dispatch
- `cli.spl` — grammar parser per state.md L810–826: `sj <jj-verb>`,
  `sj git <git-verb>`, `sj raw {jj|git}`, `sj daemon {start|stop|status|kick}`
- `client.spl` — UDS client; connects to `./.sj/daemon.sock` over
  `rt_unix_socket_connect`, sends framed JSON requests, receives JSON
  responses
- `fallback.spl` — when daemon not running, runs the request in-process
  (calls into I-B's request handler directly, no UDS hop)
- `busy_backoff.spl` — D-5 BUSY contract; retries with jitter on
  `ERROR[BUSY]:` (exit code 75) up to N times before propagating

**Wrapper (`bin/sj.cmd`):**
- Default: run `bin/simple test/run` against `src/app/sj/main.spl` (per
  R-B's MCP wrapper convention — `feedback_mcp_cache_off_by_default.md`)
- Cache: gate behind `SIMPLE_SJ_USE_CACHE=1` (matches `simple_mcp_server.cmd`)

**Spec gate:**
```bash
bin/simple test test/unit/app/sj/busy_contract_spec.spl
bin/simple test test/unit/app/sj/direct_jj_translation_spec.spl
bin/simple test test/unit/app/sj/multi_step_translation_spec.spl
bin/simple test test/unit/app/sj/raw_passthrough_spec.spl
```

**Sub-agent recipe:** mirror I-B's prompt, swap §2 → §3, swap "service
base + UDS externs" → "I-B's `RequestHandler` trait stable in
`std.service.traits`". Hard stop after 4 hours.

---

## 4. I-D — migration sweep (sequential; depends on I-A/B/C compiling)

**Estimated:** 1–2 hours. Pure rewrite; no new logic.

**Scope (per R-C's classification in state.md L941–995):**

**`migrate-now` (9 items)** — straight rewrite:
- `src/app/sync/sync.spl`
- `src/app/main_lazy_vcs_tools.spl`
- `src/lib/nogc_sync_mut/mcp/jj/vcs_collector.spl`
- `src/app/jj_app.spl`
- Plus help-text strings in 5 other files (state.md has the list)

**`migrate-with-care` (4 items)** — verify exit-code contract before+after:
- `src/lib/nogc_sync_mut/mcp/jj/jj_runner.spl` (CHOKEPOINT — central
  shellout; D-5 BUSY exit code 75 must be distinguishable from jj's 1/2/101)
- `src/app/...tools_jj_git.spl`
- `src/app/...commit.spl`
- Release doc with mixed jj/git pattern

**`keep-raw` (9 items)** — leave as direct calls, add a one-line
  comment explaining why:
- External-repo scripts (RTL toolchains, crypto libs, LLVM)
- Git hooks
- The new daemon/client themselves (cannot use sj — they ARE sj)

**`doc-only` (~10 .md files)** — wording update:
- `CLAUDE.md`, `.claude/rules/vcs.md`, agent/skill docs
- Create `doc/07_guide/quick_reference/sj_cli.md` per AC-5 (the `gg → sj git`
  shim doc)

**Setup wiring:**
- `scripts/setup.sh` — add `bin/sj` symlink alongside `bin/simple`

**Spec gate:** after I-D, the system smokes should pass:
```bash
bin/simple test test/system/sj_concurrency_spec.spl
bin/simple test test/system/sj_ghost_index_lock_spec.spl
bin/simple test test/system/sj_push_pattern_spec.spl
```

---

## 5. Phase 6 — `/refactor` + `/simplify` pass

**Estimated:** 1–2 hours. Single agent.

Targets:
- Collapse duplication between `sj` client (I-C) and daemon's in-process
  fallback path (I-C `fallback.spl`).
- Collapse duplication in the git-mimic translator (I-B `git_mimic.spl`)
  if it ended up as N hand-written handlers vs. table-driven.
- Trim any TODO comments still in code (per `.claude/rules/code-style.md`
  "NEVER convert TODO/FIXME to NOTE").

```
/refactor
/simplify
```

---

## 6. Phase 7 — verify

**Estimated:** 2–3 hours. Single agent with `/verify` skill.

Steps:
1. **Bootstrap deploy** (mandatory for compiled-mode coverage):
   ```bash
   scripts/bootstrap/bootstrap-from-scratch.sh --deploy
   ```
2. **Manually clear `.git/index.lock`** if any stale locks exist
   before this phase, so the daemon's reclaim rule (D-6) is exercised
   by **test-staged** ghost locks (per RESUME_PLAN.md §11a "Pre-Phase-7
   housekeeping" — mixing real and staged ghost locks pollutes the
   signal).
3. **Full test suite:** `bin/simple test`
4. **Concurrency smoke:** `bin/simple test test/system/sj_concurrency_spec.spl`
5. **Ghost-lock smoke:** `bin/simple test test/system/sj_ghost_index_lock_spec.spl`
6. **Parallel-claudes simulation:** spawn 2 dummy clients hammering
   the daemon while a 3rd reads, plus `sync.spl` exercising the BUSY
   contract.
7. **AC-1..AC-7 sign-off** appended to `state.md ### 7-verify`.

---

## 7. Phase 8 — ship

**Estimated:** 30 min if no contention. Single agent with `/sync` skill.

Pre-flight (per memories):
- **Pause any parallel /dev sessions** (`feedback_submodule_race_parallel_dev.md`)
- **Per-phase commits, no bundling** (`feedback_sync_bundling_clobbers_commits.md`)
- **`git diff origin/main` per-file before drafting ship commit**
  (`feedback_wip_snapshot_half_ship.md`)
- **File-count guard before+after rebase** (`feedback_destructive_upstream_detection.md`)

Push:
```bash
jj bookmark set main -r @-
jj git push --bookmark main
```

If contended, fall back to `feedback_push_via_worktree.md`:
```bash
git worktree add --detach /tmp/sj-push origin/main
cd /tmp/sj-push
git cherry-pick <commit-list>
cd -
git update-ref refs/heads/main <new-tip> <old-tip>
git push origin main --force-with-lease
```

---

## 8. Critical risks carried forward

1. **Parallel claude sessions in this repo** — they have already wiped
   untracked work once this session (recovered from git via
   `git checkout 791c57404c`). Coordinate before any phase that creates
   untracked files in bulk. Memory: `feedback_submodule_race_parallel_dev.md`.
2. **8.4 MB stale `.git/index.lock`** — appeared once this session. If
   it reappears, check `lsof` first (no live holder = stale, safe to
   `rm`). The whole point of this feature is to prevent these.
3. **D-1 `rebase -i` forbidden** — spec asserts `ERROR[FORBIDDEN]`. If
   user later wants composition or raw passthrough, that's a v2 ADR
   change, not a code-only fix.
4. **D-11 stash dropped from v1** — `sj git stash` returns `FORBIDDEN`
   with redirect to `jj new -m wip-<topic>`. Spec asserts this in
   `forbidden_verbs_spec.spl`. Don't quietly add stash back.
5. **`feedback_compile_mode_false_greens.md`** — `--mode=native` and
   `--mode=smf` swallow runtime errors. **Run all sj specs in
   interpreter mode** through Phase 6. Phase 7 may use compiled mode
   for coverage but must double-check via interpreter mode.
6. **Existing parallel-claude work** — `src/os/apps/vcs/vcs_capsule.spl`
   and `manifest.sdn` were added by the parallel session and may overlap
   with sj's design space. Read them before I-B starts; reconcile or
   coordinate with that author.

---

## 9. Cross-references

- **State file (full record):** `.sstack/jj-wrapper-daemon/state.md` (~1140 lines)
- **History/recovery:** `.sstack/jj-wrapper-daemon/RESUME_PLAN.md`
- **Design doc:** `doc/04_architecture/sj_vcs_service.md`
- **MDSOC+ template:** `doc/04_architecture/sj_mdsoc_plus_template.md`
- **MDSOC+ reference:** `doc/04_architecture/mdsoc_architecture_tobe.md`
- **VCS rules:** `.claude/rules/vcs.md`
- **Bootstrap rules:** `.claude/rules/bootstrap.md`
- **Memory dir:** `/home/ormastes/.claude/projects/-home-ormastes-dev-pub-simple/memory/`

— end of plan —
