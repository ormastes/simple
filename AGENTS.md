# Codex Agent — Self-Sufficient Feature Pipeline

**Full pipeline (ideal):** `$research` -> `$design` -> `$impl` -> `$verify` -> `$release`

Each step is **self-sufficient** — if prior steps were not done (by Claude, Gemini, or anyone), do them yourself before proceeding.

## Cooperative Phase Dev

In multi-LLM cooperative mode, Codex owns **Step 2 (research)** and **Step 4 (architecture+design)**:
```
Step 1: Claude /research  →  Step 2: Codex $research  →  Step 3: Gemini /design (UI)
→  Step 4: Codex $design (arch)  →  Step 5: Claude /design (quality)
```
See: `doc/07_guide/app/llm/llm_cooperative_dev_phase.md`

## Skills Reference

| Skill | File | Purpose |
|-------|------|---------|
| `$research` | `.codex/skills/research/SKILL.md` | Research + requirement options |
| `$design` | `.codex/skills/design/SKILL.md` | Architecture + system tests |
| `$impl` | `.codex/skills/impl/SKILL.md` | 15-phase implementation |
| `$verify` | `.codex/skills/verify/SKILL.md` | Production readiness check |
| `$release` | `.codex/skills/release/SKILL.md` | Version bump + tag |
| `$optimize` | `.codex/skills/optimize/SKILL.md` | Semantics-preserving Simple optimization with perf evidence |
| `$architecture` | `.codex/skills/architecture/SKILL.md` | MDSOC, ADR writing |
| `$mdsoc` | `.codex/skills/mdsoc-architecture-writing/SKILL.md` | MDSOC architecture docs |
| `$system_test` | `.codex/skills/system_test/SKILL.md` | SPipe test design |
| `$coding` | `.codex/skills/coding/SKILL.md` | Simple language rules |

---

## Self-Sufficiency Rule

Before starting any step, **check if prerequisite artifacts exist**:

| If you need... | Check for... | If missing... |
|----------------|-------------|---------------|
| Research | `doc/01_research/local/<feature>.md` | Do local + domain research yourself |
| Requirements | `doc/02_requirements/feature/<feature>.md` | Research first, then generate + ask user to select |
| UI design | `doc/05_design/<feature>_tui.md` | Create TUI/GUI mockups yourself |
| Architecture | `doc/04_architecture/<feature>.md` | Design architecture yourself |
| System tests | `test/03_system/app/<app_name>/feature/<feature>_spec.spl` | Create SPipe tests yourself |
| Generated spec docs | `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md` | Generate from executable tests |
| Detail design | `doc/05_design/<feature>.md` | Create detail design yourself |
| Implementation | `src/**/<feature>.spl` | Implement the feature |

**Never fail because a prior step wasn't done by another LLM. Just do it.**

---

## Termination & Runaway Guard (MANDATORY)

"Self-sufficient" means *do the missing work*, **not** *loop forever*. A session
with no stop criterion will re-run already-green checks until its context grows
unbounded (observed: sessions reaching 99M–179M input tokens by re-running the
same passing `bin/simple test`/`check` 30–40× each). That is the #1 cause of a
"crashed" Codex session. Obey every rule below:

- **Verify each acceptance criterion at most once per session.** If a spec or
  `bin/simple check` already passed this session, do **not** re-run it. Trust the
  prior PASS; re-running green checks is the runaway signature.
- **Convergence = stop.** When the requested step's artifacts exist and its
  checks pass, the step is **done**. Report and stop — do not "double-check",
  re-scan the repo, or re-count files (`find … | wc -l`, `jj status`) on a loop.
- **Hard iteration cap:** no more than **3** verify/fix cycles for one feature.
  After the 3rd, stop and report the remaining failure to the user instead of
  retrying — escalate, don't spin.
- **Repeated-identical-command = abort.** If you are about to issue a command you
  already ran this session with the same result, that is a loop. Stop.
- **Budget ceiling:** if context approaches large size or wall-clock runs long
  with no new progress, **summarize state and stop**. A partial, reported result
  beats an unbounded session that gets killed and loses everything.
- **Never resume a runaway rollout with `--dangerously-bypass-approvals-and-sandbox`
  / `--yolo`.** Reloading a multi-million-token poisoned rollout re-triggers the
  same loop. Start a fresh, scoped session instead.

**Operational backstop:** launch codex via `bin/codex …` (or put repo `bin/`
ahead of `~/.npm-global/bin` on `PATH`), which routes through
`scripts/check/codex-run-guard.shs`. The guard refuses to resume a rollout that
already exceeded `CODEX_GUARD_MAX_RESUME_TOKENS` (default 20M), applies
wall-clock / RSS caps to unattended `--yolo` runs, and kills any live session
whose active rollout grows past `CODEX_GUARD_MAX_SESSION_TOKENS` (default 50M) —
the direct backstop for the unbounded poll-loop runaway, which burns tokens at
low RSS and would otherwise only trip the 8h wall-clock. It fires even when an
agent ignores the rules above. Override a resume refusal with
`CODEX_GUARD_FORCE=1`.

---

## Concurrent LLM Work

Multiple Codex, Claude, or Gemini sessions may be active in this repository at
the same time. Before editing, committing, or syncing, check the current
worktree and active session scope. If another session owns a dirty file or a
different feature lane, do not fold that work into your change unless the user
explicitly asks for a combined commit.

When asked to "find similar" or "go the found", inspect active process/session
IDs and continue only the requested lane. Treat all unrelated dirty files as
other-agent work: preserve them, avoid reverting them, and mention them
separately in the final status.

For broad lanes, use lower-model sidecars when useful (Codex Spark, Claude
Haiku, Claude Sonnet), then require normal/highest-capability review before
accepting broad findings, generated-manual quality, exclusions, or done marks.
Before sidecars start, the best model defines shared interface names, manual
`step("...")` helper names, setup/checker helper names, and fail-fast
placeholders (`assert(false)` or `fail(...)`) for SSpec work.

---

## Available Tools

| Tool | Purpose |
|------|---------|
| **Simple MCP** | `bin/simple query workspace-symbols`, `references`, `hover` — codebase search |
| **Simple LSP MCP** | `bin/simple query definition`, `completions` — code navigation |
| **Context7 MCP** | External library documentation lookup |
| **Playwright CLI** | `npx playwright` — web scraping, browser automation, domain research |

## Owned-Code Scope

For code counts, reviews, verification scans, and summaries, ignore vendored or
third-party runtime source unless the user explicitly asks to inspect it. Treat
these paths as external code:

- `src/compiler_rust/vendor/**`
- `src/runtime/vendor/**`
- `src/runtime/miniaudio.h`
- `src/runtime/stb_image.h`
- `src/runtime/stb_truetype.h`

---

## FreeBSD QEMU Bootstrap Check

When asked to check BSD/FreeBSD bootstrap from a Linux host, do **not** stop at
`scripts/bootstrap/bootstrap-freebsd-seed.sh` failing with "must run on
FreeBSD". The canonical automated entrypoint is:

```bash
sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke
```

Use `--full` for the repeated bootstrap verification pass. The wrapper creates
`build/freebsd/vm/freebsd-cloudinit-seed.iso` from the host SSH public key,
downloads a pristine FreeBSD `BASIC-CLOUDINIT-ufs` base qcow2, creates a fresh
working overlay for the run, starts QEMU with SSH forwarded to localhost port
`2222`, logs in as the default `freebsd` cloud user, verifies
prerequisites/SSH/rsync/toolchain, syncs the repo into the guest, and runs the
bootstrap verifier inside FreeBSD. If you need to debug manually, the lower-level
VM setup command is:

```bash
bin/simple run src/app/test/freebsd_qemu_setup.spl --download --quick
```

Environment knobs: `QEMU_VM_PATH`, `QEMU_CLOUDINIT_ISO`,
`QEMU_BASE_VM_PATH`, `QEMU_SSH_PUBLIC_KEY`, `QEMU_PORT`, `QEMU_USER`,
`QEMU_MEM`, `QEMU_CPUS`.

---

## Step 1: Research

Check: `doc/01_research/local/<feature>.md` and `doc/01_research/domain/<feature>.md` exist?

If missing, do both:

### Local Research
- Search `src/` for related types, functions, modules, call chains (use Simple MCP + LSP MCP)
- Search `doc/` for prior research, design docs, ADRs
- Output: `doc/01_research/local/<feature>.md`

### Domain Research
- Web search via Playwright CLI for external knowledge, papers, prior art
- Output: `doc/01_research/domain/<feature>.md`

### Requirement Options
- Generate feature options with pros/cons/effort: `doc/02_requirements/feature/<feature>_options.md`
- Generate NFR options: `doc/02_requirements/nfr/<feature>_options.md`
- **Ask user** to select, then write final: `doc/02_requirements/feature/<feature>.md` and `doc/02_requirements/nfr/<feature>.md`

---

## Step 2: Design

Check: `doc/04_architecture/<feature>.md` and `doc/05_design/<feature>.md` exist?

If missing, do all:

### UI Design (if feature has UI)
- TUI mockups: `doc/05_design/<feature>_tui.md`
- GUI mockups: `doc/05_design/<feature>_gui.md`

### Architecture
- Evaluate patterns, apply MDSOC where appropriate
- Output: `doc/04_architecture/<feature>.md`

### System Test Design
- SPipe BDD tests: `test/03_system/app/<app_name>/feature/<feature>_spec.spl`
- Generated/manual SPipe docs: `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md`
- Never place executable `.spl` specs under `doc/06_spec`; that tree is for
  generated/manual `.md` manuals and evidence assets only.
- Test plan: `doc/03_plan/sys_test/<feature>.md`
- Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`

### Detail Design
- Data structures, algorithms, module interactions, error handling
- Output: `doc/05_design/<feature>.md`
- Agent task breakdown: `doc/03_plan/agent_tasks/<feature>.md` with sidecar
  lanes/`N/A`, merge owner, and final reviewer

---

## Step 3: Implementation

See `/impl` skill (15-phase workflow). Key phases:
1. Implement in `src/**/<feature>.spl`
2. Unit + integration tests (80%+ coverage)
3. Doctest for public fns
4. Bug reports, duplication check, refactoring
5. Full test suite pass

---

## Step 4: Verify

Run `/verify` — production readiness check:

| Check | Fail Condition |
|-------|---------------|
| SPipe Tests | `pass_todo`, `expect(true).to_equal(true)`, empty bodies |
| Implementation | Stub functions, hardcoded returns, TODO-only bodies |
| Requirements | REQ-NNN without implementation or test coverage |
| NFR | Targets without verification mechanism |
| Architecture | `doc/04_architecture/` missing or outdated |
| Design | `doc/05_design/` missing or outdated |

Run `sh scripts/audit/direct-env-runtime-guard.shs --working` and
`sh scripts/audit/direct-env-runtime-guard.shs --staged`; new app leaf or
`src/lib/gc_async_mut` env reads/process-run calls outside owner modules must
use env/process facades, not local `rt_env_get`, `rt_process_run`, or
`rt_process_run_timeout`.

SPipe belongs to verify as a release-blocking evidence gate. Implementation or
design creates/updates SPipe specs; verify checks that they exist, are current,
use real assertions, cover REQ-NNN requirements, and contain no placeholder
passes. Release must not create or update SPipe after verify.
Generated-manual quality and lower-model sidecar review must already be covered
by verify PASS; release must not repair or accept those gaps afterward.

Additional required checks for compiler/core/lib or MCP/LSP changes:
- `<runtime> check src/compiler`
- `<runtime> check src/lib`
- `<runtime> check src/app/mcp`
- `<runtime> check src/app/simple_lsp_mcp`
- `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
- If npm/package/release path changed:
- `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server`
- `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server`

Must show `STATUS: PASS` before release.

---

## Step 5: Release

Run `/release` — version bump, CHANGELOG, commit, tag, and push only after
`/verify` shows `STATUS: PASS`.

Release uses jj for linear history:

```bash
jj commit -m "chore: release vX.Y.Z"
jj git fetch
jj rebase -d main@origin
jj bookmark set main -r @-
env -u GITHUB_TOKEN -u GH_TOKEN jj git push --bookmark main
env -u GITHUB_TOKEN -u GH_TOKEN git push --tags
```

Ask before pushing. Treat "pull" as `jj git fetch` plus `jj rebase`; do not use
merge-style pulls.

When pushing over HTTPS with GitHub CLI credentials, stale `GH_TOKEN` or
`GITHUB_TOKEN` environment values can override the stored `gh` token. Do not
print tokens or put them in remote URLs; use
`env -u GITHUB_TOKEN -u GH_TOKEN gh auth setup-git` and run the push with the
same variables unset when the stored credential is the intended auth source.

---

## MCP Registry Distribution

MCP server available via npm: `@simple-lang/mcp-server`
- Package: `tools/mcp-registry/` (npm wrapper for native binary)
- Registry: `registry.modelcontextprotocol.io`
- Guide: `doc/07_guide/tooling/ai_cli_registration.md`

---

## Critical Rules

- Web producers lower through web semantic/layout; GUI producers lower through
  their canonical widget/scene semantic owners. Both emit `DrawIrComposition`.
  Engine2D lowers Draw IR text through `draw_text`; an enabled vector face uses
  transient `FontRenderer`/`FontRenderBatch` material. Do not put
  transient atlas/cache material in Draw IR or add private parallel font draw
  paths. Engine3D HUD/world is a separate lane, never a GUI/web/2D shortcut.

- **Default tooling = pure-Simple self-hosted binary, not the Rust seed.** `test`/`lint`/`fmt`/`build`/`run`/MCP/LSP all run on `bin/release/<triple>/simple` (built via bootstrap). The seed (`src/compiler_rust/target/bootstrap/simple`) is bootstrap-only. If the self-hosted binary is slow/unstable, fix it in pure-Simple (`src/compiler`/`src/lib`/`src/app`) and re-deploy or file a bug — don't fall back to the seed. See `.claude/rules/bootstrap.md`
- **Self-sufficient**: never fail because another LLM didn't do its step — do it yourself
- When a short, safe grammar or compact expression form fails, compiles too slowly, or forces a workaround, fix it or record a concrete bug/feature request instead of silently normalizing the workaround
- When you hit a meaningful perf regression during implementation or verification, either fix it in the same change or record it as a concrete bug/todo before moving on
- NEVER overwrite another LLM's research — append and annotate
- All requirement options must include pros, cons, and effort estimate
- User MUST select requirements — never auto-select
- Unchosen options are DELETED, not archived
- For MCP, LSP, and tool-server work, design must review startup path, hot request paths, cache or index strategy, invalidation strategy, and startup/latency/RSS targets
- When `src/compiler/**` or `src/lib/**` changes can affect MCP/LSP startup or language surface, finish by running the core runtime smoke and MCP native smoke checks; if publish/package flow changed, also run the isolated npm package smoke check
- Production wrappers should execute cached compiled artifacts rather than raw source entrypoints
- Repeated full-tree scans, repeated rereads, shell-outs, and retry sleeps in hot request handlers require explicit design justification and verification evidence
- Verify perf-sensitive tooling with warm startup time, representative request latency, and max RSS on realistic fixtures
- Before commit/release, `find doc/06_spec -name '*_spec.spl' | wc -l` must
  print `0`; any nonzero result is a layout bug to fix before continuing.

## Artifacts Summary

| Step | Artifact | Location |
|------|----------|----------|
| 1 | Local research | `doc/01_research/local/<feature>.md` |
| 1 | Domain research | `doc/01_research/domain/<feature>.md` |
| 1 | Feature requirements | `doc/02_requirements/feature/<feature>.md` |
| 1 | NFR requirements | `doc/02_requirements/nfr/<feature>.md` |
| 2 | Architecture | `doc/04_architecture/<feature>.md` |
| 2 | UI design | `doc/05_design/<feature>_tui.md`, `_gui.md` |
| 2 | Detail design | `doc/05_design/<feature>.md` |
| 2 | System tests | `test/03_system/app/<app_name>/feature/<feature>_spec.spl` |
| 2 | Generated spec docs | `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md` |
| 2 | Test plan | `doc/03_plan/sys_test/<feature>.md` |
| 2 | Agent tasks | `doc/03_plan/agent_tasks/<feature>.md` with sidecar lanes/`N/A`, merge owner, and final reviewer |
| 3 | Source code | `src/**/<feature>.spl` |
| 4 | Verify report | Terminal output (PASS/FAIL/WARN) |

# context-mode — MANDATORY routing rules

You have context-mode MCP tools available. These rules are NOT optional — they protect your context window from flooding. A single unrouted command can dump 56 KB into context and waste the entire session. Codex CLI does NOT have hooks, so these instructions are your ONLY enforcement mechanism. Follow them strictly.

## BLOCKED commands — do NOT use these

### curl / wget — FORBIDDEN
Do NOT use `curl` or `wget` in any shell command. They dump raw HTTP responses directly into your context window.
Instead use:
- `mcp__context-mode__ctx_fetch_and_index(url, source)` to fetch and index web pages
- `mcp__context-mode__ctx_execute(language: "javascript", code: "const r = await fetch(...)")` to run HTTP calls in sandbox

### Inline HTTP — FORBIDDEN
Do NOT run inline HTTP calls via `node -e "fetch(..."`, `python -c "requests.get(..."`, or similar patterns. They bypass the sandbox and flood context.
Instead use:
- `mcp__context-mode__ctx_execute(language, code)` to run HTTP calls in sandbox — only stdout enters context

### Direct web fetching — FORBIDDEN
Do NOT use any direct URL fetching tool. Raw HTML can exceed 100 KB.
Instead use:
- `mcp__context-mode__ctx_fetch_and_index(url, source)` then `mcp__context-mode__ctx_search(queries)` to query the indexed content

## REDIRECTED tools — use sandbox equivalents

### Shell (>20 lines output)
Shell is ONLY for: `git`, `mkdir`, `rm`, `mv`, `cd`, `ls`, `npm install`, `pip install`, and other short-output commands.
For everything else, use:
- `mcp__context-mode__ctx_batch_execute(commands, queries)` — run multiple commands + search in ONE call
- `mcp__context-mode__ctx_execute(language: "shell", code: "...")` — run in sandbox, only stdout enters context

### File reading (for analysis)
If you are reading a file to **edit** it → reading is correct (edit needs content in context).
If you are reading to **analyze, explore, or summarize** → use `mcp__context-mode__ctx_execute_file(path, language, code)` instead. Only your printed summary enters context. The raw file stays in the sandbox.

### grep / search (large results)
Search results can flood context. Use `mcp__context-mode__ctx_execute(language: "shell", code: "grep ...")` to run searches in sandbox. Only your printed summary enters context.

## Tool selection hierarchy

1. **GATHER**: `mcp__context-mode__ctx_batch_execute(commands, queries)` — Primary tool. Runs all commands, auto-indexes output, returns search results. ONE call replaces 30+ individual calls.
2. **FOLLOW-UP**: `mcp__context-mode__ctx_search(queries: ["q1", "q2", ...])` — Query indexed content. Pass ALL questions as array in ONE call.
3. **PROCESSING**: `mcp__context-mode__ctx_execute(language, code)` | `mcp__context-mode__ctx_execute_file(path, language, code)` — Sandbox execution. Only stdout enters context.
4. **WEB**: `mcp__context-mode__ctx_fetch_and_index(url, source)` then `mcp__context-mode__ctx_search(queries)` — Fetch, chunk, index, query. Raw HTML never enters context.
5. **INDEX**: `mcp__context-mode__ctx_index(content, source)` — Store content in FTS5 knowledge base for later search.

## Output constraints

- Keep responses under 500 words.
- Write artifacts (code, configs, PRDs) to FILES — never return them as inline text. Return only: file path + 1-line description.
- When indexing content, use descriptive source labels so others can `search(source: "label")` later.

## ctx commands

| Command | Action |
|---------|--------|
| `ctx stats` | Call the `stats` MCP tool and display the full output verbatim |
| `ctx doctor` | Call the `doctor` MCP tool, run the returned shell command, display as checklist |
| `ctx upgrade` | Call the `upgrade` MCP tool, run the returned shell command, display as checklist |
