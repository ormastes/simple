# Simple Language Compiler

**Self-hosted compiler written in Simple.** Bootstrap: Rust seed → Simple compiler → self-hosted binary.
Impl in Simple unless it has big performance differences.

## Essential Commands
```bash
bin/simple build                  # Prints bootstrap HELP and exits (~0.02s) — does NOT build
                                  # A src/lib/** edit needs NO build: stdlib is read as SOURCE
                                  # every run (82 .spl opens, 0 .smf). Bootstrap only DEPLOYS a
                                  # compiler. See .claude/rules/commands.md
bin/simple test                   # Run all tests (or: test path/to/spec.spl)
scripts/setup/setup.shs && bin/simple build bootstrap  # NOT the sanctioned bootstrap.
   # `build bootstrap` is a SEPARATE seed-side Rust reimplementation of a 3-stage
   # self-compilation check (misc_commands.rs:341 handle_bootstrap). It does not run
   # scripts/bootstrap/bootstrap-from-scratch.sh, has no receipt gate, no planner
   # admission, and no Stage 4 / full-CLI relink. The sanctioned bootstrap is the
   # script — see .claude/rules/bootstrap.md and doc/07_guide/tooling/bootstrap_options.md.
```

## FreeBSD QEMU Bootstrap Check
From Linux, do not stop at `bootstrap-freebsd-seed.sh` saying it must run on
FreeBSD. Use the repo-managed automated wrapper:

```bash
sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke
```

Use `--full` for the repeated bootstrap verification pass. The wrapper creates
`build/freebsd/vm/freebsd-cloudinit-seed.iso` from the host SSH public key,
downloads a pristine FreeBSD `BASIC-CLOUDINIT-ufs` base qcow2, creates a fresh
working overlay for the run, starts QEMU with SSH forwarding on port `2222`, and
logs in as the default `freebsd` cloud user. Env knobs: `QEMU_VM_PATH`,
`QEMU_BASE_VM_PATH`, `QEMU_CLOUDINIT_ISO`, `QEMU_SSH_PUBLIC_KEY`, `QEMU_PORT`,
`QEMU_USER`, `QEMU_MEM`, `QEMU_CPUS`. For manual VM debugging:

```bash
bin/simple run src/app/test/freebsd_qemu_setup.spl --download --quick
```

## Critical Rules
- **jj** for VCS — commit: `jj commit -m "msg"` (git fallback: `git commit` when jj is absent)
- **Land via PR, never direct push** — `main` is ruleset-protected (since 2026-09-05: PR required, 2 required checks, no bypass). Push to a short-lived topic branch, `gh pr create`, `gh pr merge --merge`, delete the branch. Topic branches exist ONLY to carry a PR — no long-lived feature branches. See `.claude/rules/vcs.md`
- **ALL code in `.spl`/`.shs`** — no Python/Bash (except 3 bootstrap scripts)
- **NO inheritance** — use composition, traits, mixins. **Generics:** `<>` not `[]`
- **NEVER skip** failing tests without approval. **NEVER convert TODO to NOTE** — implement or delete
- When a short, safe grammar or compact expression form fails, compiles too slowly, or forces a workaround, fix it or record a concrete bug/feature request instead of silently normalizing the workaround
- When you hit a meaningful perf regression during implementation or verification, either fix it in the same change or record it as a concrete bug/todo before moving on
- **NEVER over-engineer.** **DO NOT ADD REPORT TO GIT** unless requested
- **Default tooling = pure-Simple self-hosted binary, not the Rust seed.** `test`/`lint`/`fmt`/`build`/`run`/MCP/LSP all run on `bin/release/<triple>/simple` (built via bootstrap). Seed is bootstrap-only. If the self-hosted binary is slow/unstable, fix it in pure-Simple and re-deploy or file a bug — don't fall back to the seed. See `.claude/rules/bootstrap.md`
- **MDSOC+ by default** — use MDSOC outer + ECS business layer for userland services/apps; kernel/drivers stay MDSOC-only. See `doc/04_architecture/compiler/mdsoc_architecture_tobe.md` (MDSOC+ section)

## Owned-Code Scope
- For code counts, reviews, verification scans, and summaries, ignore vendored or third-party runtime source unless the user explicitly asks to inspect it.
- External paths: `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`, `src/runtime/miniaudio.h`, `src/runtime/stb_image.h`, `src/runtime/stb_truetype.h`.

## Detailed Rules & Reference
- **Rules:** `.claude/rules/` — `language.md`, `testing.md`, `bootstrap.md`, `commands.md`, `structure.md`, `code-style.md`, `vcs.md`
- **Skills:** `.claude/skills/` — invoke `/skill-name`; Codex development uses `$sp_dev` for the SPipe dev entrypoint
- **Agents:** `.claude/agents/` — `code`, `test`, `debug`, `explore`, `docs`, `vcs`, `infra`, `build`, `ml`, `perf`, `mem`
- **Memory refs:** `.claude/memory/ref_*.md` — architecture, coding, SFFI, stdlib, CUDA, etc.
- **Syntax:** `doc/07_guide/quick_reference/syntax_quick_reference.md`

# context-mode — MANDATORY routing rules

You have repo-native `simple_ctx_*` MCP tools available (`app.mcp.main_lazy_ctx_tools`, server `simple-mcp` / `simple-pipe-mcp`). These rules are NOT optional — they protect your context window from flooding. A single unrouted command can dump large output into context and waste the entire session.

**Provenance note:** this section used to route to the user-level `context-mode` plugin's bare `ctx_*` tool names. That plugin's tools are gone; this section now points at the repo's own `simple_ctx_*` MCP tools, which are a superset with a persistent, repo-scoped `.simple/ctx/` store (survives process restarts, unlike the plugin's per-process temp DB) — see `doc/07_guide/app/mcp/mcp.md` and `src/app/mcp/main_lazy_ctx_tools.spl` for the full contract. The Bash `curl`/`wget`/inline-HTTP and `WebFetch` blockers below are no longer plugin behavior either — they are enforced by project hooks in `.claude/hooks/` (`bash_net_blocker.shs`, `webfetch_deny.shs`), wired via `PreToolUse` in `.claude/settings.json`, and fail CLOSED on malformed input.

## BLOCKED commands — do NOT attempt these

### curl / wget — BLOCKED
Any Bash command containing `curl` or `wget` is intercepted and replaced with an error message. Do NOT retry.
Instead use:
- `simple_ctx_fetch_and_index(url, source)` to fetch and index web pages
- `simple_ctx_execute(language: "javascript", code: "const r = await fetch(...)")` to run HTTP calls in sandbox

### Inline HTTP — BLOCKED
Any Bash command containing `fetch('http`, `requests.get(`, `requests.post(`, `http.get(`, or `http.request(` is intercepted and replaced with an error message. Do NOT retry with Bash.
Instead use:
- `simple_ctx_execute(language, code)` to run HTTP calls in sandbox — only stdout enters context

### WebFetch — BLOCKED
WebFetch calls are denied entirely. The URL is extracted and you are told to use `simple_ctx_fetch_and_index` instead.
Instead use:
- `simple_ctx_fetch_and_index(url, source)` then `simple_ctx_search(queries)` to query the indexed content

## REDIRECTED tools — use sandbox equivalents

### Bash (>20 lines output)
Bash is ONLY for: `git`, `mkdir`, `rm`, `mv`, `cd`, `ls`, `npm install`, `pip install`, and other short-output commands.
For everything else, use:
- `simple_ctx_batch_execute(commands, queries)` — run multiple commands + search in ONE call
- `simple_ctx_execute(language: "shell", code: "...")` — run in sandbox, only stdout enters context

### Read (for analysis)
If you are reading a file to **Edit** it → Read is correct (Edit needs content in context).
If you are reading to **analyze, explore, or summarize** → use `simple_ctx_execute_file(path, language, code)` instead. Only your printed summary enters context. The raw file content stays in the sandbox.

### Grep (large results)
Grep results can flood context. Use `simple_ctx_execute(language: "shell", code: "grep ...")` to run searches in sandbox. Only your printed summary enters context.

## Tool selection hierarchy

1. **GATHER**: `simple_ctx_batch_execute(commands, queries)` — Primary tool. Runs all commands, indexes output, returns search results. ONE call replaces many individual calls.
2. **FOLLOW-UP**: `simple_ctx_search(queries: ["q1", "q2", ...])` — Query indexed content. Pass ALL questions as array in ONE call.
3. **PROCESSING**: `simple_ctx_execute(language, code)` | `simple_ctx_execute_file(path, language, code)` — Sandbox execution. Only stdout enters context; stderr is summarized to one line.
4. **WEB**: `simple_ctx_fetch_and_index(url, source)` then `simple_ctx_search(queries)` — Fetch (size-capped, tags stripped), chunk, index, query. Raw HTML never enters context.
5. **INDEX**: `simple_ctx_index(content, source)` — Chunk and index text into the persistent BM25 store for later search.

## Subagent routing

Subagents launched via the Agent/Task tool inherit this project's `CLAUDE.md` automatically — Claude Code loads project instructions from the working directory for every session and subagent, not just the top-level one, so this routing section reaches spawned subagents without any extra injection step. **This has not been independently re-verified inside this repo** (no in-repo test exercises subagent CLAUDE.md inheritance), so treat it as the documented Claude Code harness behavior rather than a repo-proven guarantee; if a subagent is ever observed calling raw shell instead of `simple_ctx_*` tools, that is the place to check first.

**Residual gap (honest, not closed):** the plugin additionally claimed it auto-upgraded Bash-type subagents to general-purpose so they'd have MCP tool access. There is no repo equivalent of that upgrade step — it lived entirely in the plugin's injection logic. A subagent explicitly typed as a tool-restricted agent (see `.claude/agents/*.md` frontmatter) may still lack access to the `simple_ctx_*` tools even though it can read this routing text; this section documents the rule, it does not grant the tool access.

## Output constraints

- Keep responses under 500 words.
- Write artifacts (code, configs, PRDs) to FILES — never return them as inline text. Return only: file path + 1-line description.
- When indexing content, use descriptive source labels so others can `simple_ctx_search(source: "label")` later.

## ctx commands

| Command | Action |
|---------|--------|
| `ctx stats` | Call the `simple_ctx_stats` MCP tool and display the full output verbatim |
| `ctx doctor` | Call the `simple_ctx_doctor` MCP tool and display its checklist verbatim |
| `ctx upgrade` | Call the `simple_ctx_upgrade` MCP tool and display its before/after report verbatim |
