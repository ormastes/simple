# Plan: SPipe Plugin Simple-Language Migration (staged, Option C)

Date: 2026-09-24. Research: doc/01_research/local/spipe_plugin_simple_migration.md,
doc/01_research/domain/spipe_plugin_simple_migration.md.
Requirements: doc/02_requirements/feature/spipe_plugin_simple_migration_options.md
(Option C selected as pragmatic default — user is running under goal mode and
is not available for the normal mandatory option selection; all four options
are preserved in the requirements doc so the user can override at review).

## Preconditions / invariants

- The uncommitted `.spipe/spipe/doc/00_llm_process/spipe/skill.md` edit
  (Trap section, line 370) belongs to another agent — never stage it.
- Submodule is DETACHED at 155d58a; origin/main is 6e1d8db. Before
  branching run `git fetch origin` and `git merge-base --is-ancestor` to
  decide the base (prefer a new branch off origin/main; do not build on the
  detached docgen commit unless main lacks it).

## Phase 0 — Branch + guard (Spipe repo)

1. `cd .spipe/spipe && git fetch origin`.
2. `git checkout -b work/spipe-simple-migration origin/main` (base TBD per
   merge-base check above).
3. Confirm `git status` shows only the skill.md modification; leave it dirty.

## Phase 1 — Scaffolding + MCP server (Spipe repo)

4. Add `src/` layout (new, Simple sources; host resolves `std.*` via its
   SIMPLE_LIB when running from a host checkout):
   - `src/spipe_mcp/main.spl` — MCP server on `std.mcp_sdk`
     (`mcp_server_init` / `mcp_server_tool` / `mcp_serve`); port the 6 tools
     and `spipe://skill` resource from `mcp/server.js:22-171`; accept the
     SDK protocolVersion bump (2024-11-05 → 2025-06-18) and standard
     JSON-RPC error codes as intended behavior changes.
   - `src/spipe_cli/main.spl` + `src/spipe_cli/{info,experts,links,doctor,
     docs}.spl` — core subcommands; manual argv dispatch like
     `src/app/mcp/main.spl`; `doc-link` uses `shell_bool("ln -s …")` on
     POSIX and `cmd /c mklink /J` on Windows until stdlib grows symlink APIs
     (file host bug: rt_symlink/rt_readlink/rt_chmod externs).
   - `src/spipe_cli/finetune.spl` — stage 2 placeholder printing
     "not yet ported; run via node fallback".
5. Keep `cli/spipe.js`, `mcp/server.js` untouched in stage 1.
6. Wrappers mirroring host bin/ style:
   - `bin/spipe` (sh) and `bin/spipe-mcp` (sh): prefer native exe from
     `build/simple-bin/` or host-provided `SPIPE_NATIVE`; else
     `simple run <entry>` with `SIMPLE_LIB` inherited.
   - `bin/spipe.cmd` / `bin/spipe-mcp.cmd`: mirror
     `bin/simple_mcp_server.cmd` — sha256-admitted native exe, else runtime
     source mode with `SIMPLE_EXECUTION_MODE=interpreter` and per-process
     stderr dirs under %TEMP%\simple.
7. `plugin/.codex-plugin/plugin.json`: point `mcpServers.spipe` at
   `bin/spipe-mcp` (and `plugin/manifest.sdn` `cli:`/`mcp:` at the new
   wrappers), keeping the Node path documented as fallback.

## Phase 2 — Tests (both repos)

8. SPipe repo `test/` (run FROM a host checkout; spipe repo has no runtime):
   - BDD spec + a shell parity harness `test/parity.sh` diffing
     `node cli/spipe.js <cmd>` vs `bin/spipe <cmd>` output for every ported
     subcommand (info/experts/link-plan/doc-root/doctor/skill/
     fine-tune-guide/fine-tune-model-guide/fine-tune-template) in a mktemp
     host.
   - MCP: scripted 4-message handshake against both servers; responses equal
     modulo protocolVersion.
9. Host repo: mirror system specs under
   `test/03_system/app/spipe/feature/spipe_simple_migration_spec.spl`
   covering the REQ ids added with the requirements doc; run
   `bin/simple test … --mode=interpreter`.
10. Update `scripts/build.sh`: keep all current checks (still Node-backed
    for fine-tune), ADD `.spl` checks — runtime presence gate, handshake
    smoke against `bin/spipe-mcp`, core CLI smoke, parity harness when node
    is available. `node --check` stays until stage 2 (NFR-A4).

## Phase 3 — PR to Spipe main (approval checkpoint #1)

11. In the submodule: commit ONLY migration files (verify
    `git status` — skill.md must remain unstaged). The Spipe repo uses
    plain git (no jj): branch `work/spipe-simple-migration`, push to origin.
12. `gh pr create --repo ormastes/Spipe --base main --title "feat: migrate
    SPipe MCP server and core CLI to Simple"` with parity evidence in the
    body. Per AGENTS.md, pushing requires explicit user approval — stop here
    and ask.

## Phase 4 — Host submodule bump (approval checkpoint #2)

13. After PR merge: `cd .spipe/spipe && git fetch origin && git checkout
    <merge-sha>` (detached, matching host convention, or follow whatever
    pointer the repo standardizes on).
14. Host repo: `sh scripts/check/check-spipe-submodule-gitlinks.shs --check`,
    run the new host specs + `sh .spipe/spipe/scripts/build.sh`.
15. Commit in host with jj per AGENTS.md release conventions; push and PR
    only with user approval. Verify whether the `examples/05_stdlib/spipe`
    gitlink must move together with `.spipe/spipe` per the gitlink guard.

## Phase 5 (follow-up PR) — Fine-tune family + Node removal

16. Port `fine-tune-*` (~1200 lines) into `src/spipe_cli/finetune_*.spl`
    command-by-command behind the parity harness; registry appends use
    `file_append_text`; scaffolds write via `file_write`; chmod via
    `shell_bool("chmod +x")` (POSIX) / no-op (Windows).
17. When parity is green: delete `cli/spipe.js`, `mcp/server.js`, drop
    `node --check` from build.sh, retarget package.json bin to wrappers
    (NFR-A4 satisfied). Bump minor version; CHANGELOG entry.

## Verify gates (before each push)

- `sh .spipe/spipe/scripts/build.sh` → `spipe_build_status=pass`.
- `bin/simple test test/03_system/app/spipe/feature/spipe_simple_migration_spec.spl --mode=interpreter` green.
- Parity harness: zero diffs on ported commands (POSIX + Windows for the
  .cmd path).
- `find doc/06_spec -name '*_spec.spl' | wc -l` == 0 in host.

## Risks / open questions

- Symlink/chmod stdlib gap → shell delegation now, host bug for rt externs.
- `std.mcp_sdk` availability: plugin .spl only runs on a host Simple runtime
  or a native build with `--source <host>/src/lib`; document this runtime
  requirement in the spipe README (npm install alone no longer sufficient).
- protocolVersion/error-code behavior deltas must be called out in the PR.
- Base-branch ambiguity (155d58a vs 6e1d8db) resolved by merge-base in
  Phase 0; if main lacks the docgen commit, ask the user whether to base on
  it instead.
