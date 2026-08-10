# MCP Failures and Interpreter Performance

## Raw Request

`$sp_dev fix mcp failures. if interpreter slow fiz perf`

## Task Type

bug

## Refined Goal

Make the canonical Simple MCP checks pass through the user-facing pure-Simple
toolchain, fixing the pure-Simple owner of each reproduced failure and removing
any measured interpreter bottleneck that makes the focused MCP gate impractical.

## Acceptance Criteria

1. **AC-1 — ownership:** Claim the applicable tracked MCP bug record before
   source edits and keep unrelated concurrent worktree changes untouched.
2. **AC-2 — exact reproduction:** Record a bounded pre-fix result and elapsed
   time for `SIMPLE_LIB=src bin/simple test
   test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`.
3. **AC-3 — adjacent reproduction:** Run at least one focused adjacent MCP
   regression (unit or native smoke) that exercises the same root-cause path.
4. **AC-4 — owner-boundary fix:** Inspect and fix the pure-Simple owner under
   `src/app/mcp`, `src/app/simple_lsp_mcp`, `src/lib`, or `src/compiler` first.
   Rust/runtime changes are permitted only if the bug record proves correct
   pure-Simple delegation and locates the defect below that boundary.
5. **AC-5 — correctness:** The exact reproducer and adjacent regression pass
   with real assertions and no placeholder success.
6. **AC-6 — interpreter performance:** If the exact gate is slow, retain a
   before/after wall-time and max-RSS comparison on the same command/fixture;
   fix the measured hot path or record a concrete remaining performance bug
   with file:line evidence and an unblock condition.
7. **AC-7 — required MCP gates:** Focused lint and duplicate-check pass for
   changed Simple files, followed once by applicable `check src/compiler`,
   `check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`, MCP
   stdio integration, native MCP smoke, and direct-env runtime guards.
8. **AC-8 — knowledge update:** Refresh affected research/architecture/design/
   plan docs or mark them N/A with reasons; update the reachable user-facing
   MCP developer guide; update/create the MCP feature expert and affected layer
   expert skills; resolve fixed bug ownership and record every remaining gap in
   `doc/08_tracking/bug/` with file:line and unblock condition. Workflow and
   generated SSpec documentation are N/A unless this fix changes their contract.

## Scope Exclusions

- Unrelated MCP protocols (T32, serial, third-party connector servers) unless a
  reproduced failure shares the same root cause.
- Release, version bump, commit, tag, or push.
- Existing dirty files owned by concurrent sessions.

## Cooperative Review

- Sidecar lanes: N/A (not requested; current repository has active independent
  sessions and this lane is kept narrowly owned).
- Merge owner: Codex `/root`.
- Final reviewer: Codex `/root` using focused and mandatory repository gates.

## Phase

implementation in progress; fresh compiler deployment required for runtime proof

## Log

- dev: Created state file with 8 acceptance criteria (type: bug).
- reproduce: Started the exact bounded interpreter gate; no source edits made.
- reproduce: Exact gate killed before scenarios at 68.18s / 1,337,660 KiB;
  raised-watchdog diagnostic stopped at 111.33s / 2,503,188 KiB before scenarios.
- research: Located unconditional non-check whole-source bulk load at
  `src/compiler/80.driver/driver_source_pipeline_loading.spl:268`.
- adjacent: Native smoke failed: wrapper contracts pass, admitted MCP/LSP
  artifacts are missing, and `rt_file_is_char_device` is absent from the JIT
  runtime provider despite correct pure-Simple, interpreter, and C ownership.
- ownership: Compiler/test-runner and Rust runtime-symbol files are currently
  dirty under active external sessions; this lane will not overwrite them.
- build: Canonical MCP native-build entered the interpreted
  `native_build_worker.spl` path but produced no build phase/artifact after
  4m35s at ~100% CPU and ~2.73 GiB RSS; stopped as the same perf reproducer.
- next: After active compiler/runtime owners settle, implement general
  interpreted single-entry import-closure loading, register the missing JIT
  symbol, rebuild MCP/LSP artifacts, then execute AC-5 through AC-8 once.
- impl: Updated the clean pure-Simple source-loader owner so explicit
  `CompileMode.Interpret` uses lazy module resolution instead of whole-project
  bulk loading. JIT/native compilation behavior is unchanged.
- regression: Added
  `test/01_unit/compiler/driver/interpret_lazy_project_sources_spec.spl` for
  the bulk-load exclusion and retained `SIMPLE_LIB` lazy resolution.
- knowledge: Updated the MCP guide with a non-reachability caveat and added MCP
  runtime plus compiler-driver expert entries. Research/architecture/detail
  design/plan changes are N/A: this is a localized restoration of the existing
  interpreter lazy-resolution architecture, not a new interface or topology.
- verify: `git diff --check` passed. Focused test and check commands cannot
  reach their target under the stale deployed binary because their own
  interpreted app entry hits the pre-fix bulk loader; fresh deployment remains
  required. The overlapping JIT runtime-provider edit remains pending.
- cleanup: Terminated the orphaned MCP `native_build_worker.spl` child left by
  the earlier parent termination; unrelated build processes were not touched.
- blocked audit 3: The same external ownership condition has now persisted for
  three consecutive goal turns. The deployed binary is still the unchanged
  2026-08-09 artifact, the active Stage-3 build has run for more than 23 minutes
  at ~21.6 GiB RSS without deploying, and the JIT runtime-symbol/test-runner
  owner files remain dirty under other sessions. Continuing cannot produce
  trustworthy fresh-binary evidence or safely repair the overlapping JIT
  provider until that external state changes.
