# Simple Language Compiler

**Self-hosted compiler written in Simple.** Bootstrap: Rust seed → Simple compiler → self-hosted binary.
Impl in Simple unless it has big performance differences.

## Essential Commands
```bash
bin/simple build                  # Debug build (lint/fmt/check/bootstrap subcommands also available)
bin/simple test                   # Run all tests (or: test path/to/spec.spl)
scripts/bootstrap/bootstrap-from-scratch.sh --deploy  # Full bootstrap
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
- **jj** for VCS — commit: `jj commit -m "msg"` / preferred wrapper flow: `sj bookmark set main -r @- && sj git push --bookmark main`
- **NEVER create branches** — work directly on `main`
- **ALL code in `.spl`/`.shs`** — no Python/Bash (except 3 bootstrap scripts)
- **NO inheritance** — use composition, traits, mixins. **Generics:** `<>` not `[]`
- **NEVER skip** failing tests without approval. **NEVER convert TODO to NOTE** — implement or delete
- When a short, safe grammar or compact expression form fails, compiles too slowly, or forces a workaround, fix it or record a concrete bug/feature request instead of silently normalizing the workaround
- When you hit a meaningful perf regression during implementation or verification, either fix it in the same change or record it as a concrete bug/todo before moving on
- **NEVER over-engineer.** **DO NOT ADD REPORT TO GIT** unless requested
- **MDSOC+ by default** — use MDSOC outer + ECS business layer for userland services/apps; kernel/drivers stay MDSOC-only. See `doc/04_architecture/mdsoc_architecture_tobe.md` (MDSOC+ section)

## Owned-Code Scope
- For code counts, reviews, verification scans, and summaries, ignore vendored or third-party runtime source unless the user explicitly asks to inspect it.
- External paths: `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`, `src/runtime/miniaudio.h`, `src/runtime/stb_image.h`, `src/runtime/stb_truetype.h`.

## Detailed Rules & Reference
- **Rules:** `.claude/rules/` — `language.md`, `testing.md`, `bootstrap.md`, `commands.md`, `structure.md`, `code-style.md`, `vcs.md`
- **Skills:** `.claude/skills/` — invoke `/skill-name`; Codex development uses `$sp_dev` for the SPipe dev entrypoint
- **Agents:** `.claude/agents/` — `code`, `test`, `debug`, `explore`, `docs`, `vcs`, `infra`, `build`, `ml`
- **Memory refs:** `.claude/memory/ref_*.md` — architecture, coding, SFFI, stdlib, CUDA, etc.
- **Syntax:** `doc/07_guide/quick_reference/syntax_quick_reference.md`

# context-mode — MANDATORY routing rules

You have context-mode MCP tools available. These rules are NOT optional — they protect your context window from flooding. A single unrouted command can dump 56 KB into context and waste the entire session.

## BLOCKED commands — do NOT attempt these

### curl / wget — BLOCKED
Any Bash command containing `curl` or `wget` is intercepted and replaced with an error message. Do NOT retry.
Instead use:
- `ctx_fetch_and_index(url, source)` to fetch and index web pages
- `ctx_execute(language: "javascript", code: "const r = await fetch(...)")` to run HTTP calls in sandbox

### Inline HTTP — BLOCKED
Any Bash command containing `fetch('http`, `requests.get(`, `requests.post(`, `http.get(`, or `http.request(` is intercepted and replaced with an error message. Do NOT retry with Bash.
Instead use:
- `ctx_execute(language, code)` to run HTTP calls in sandbox — only stdout enters context

### WebFetch — BLOCKED
WebFetch calls are denied entirely. The URL is extracted and you are told to use `ctx_fetch_and_index` instead.
Instead use:
- `ctx_fetch_and_index(url, source)` then `ctx_search(queries)` to query the indexed content

## REDIRECTED tools — use sandbox equivalents

### Bash (>20 lines output)
Bash is ONLY for: `git`, `mkdir`, `rm`, `mv`, `cd`, `ls`, `npm install`, `pip install`, and other short-output commands.
For everything else, use:
- `ctx_batch_execute(commands, queries)` — run multiple commands + search in ONE call
- `ctx_execute(language: "shell", code: "...")` — run in sandbox, only stdout enters context

### Read (for analysis)
If you are reading a file to **Edit** it → Read is correct (Edit needs content in context).
If you are reading to **analyze, explore, or summarize** → use `ctx_execute_file(path, language, code)` instead. Only your printed summary enters context. The raw file content stays in the sandbox.

### Grep (large results)
Grep results can flood context. Use `ctx_execute(language: "shell", code: "grep ...")` to run searches in sandbox. Only your printed summary enters context.

## Tool selection hierarchy

1. **GATHER**: `ctx_batch_execute(commands, queries)` — Primary tool. Runs all commands, auto-indexes output, returns search results. ONE call replaces 30+ individual calls.
2. **FOLLOW-UP**: `ctx_search(queries: ["q1", "q2", ...])` — Query indexed content. Pass ALL questions as array in ONE call.
3. **PROCESSING**: `ctx_execute(language, code)` | `ctx_execute_file(path, language, code)` — Sandbox execution. Only stdout enters context.
4. **WEB**: `ctx_fetch_and_index(url, source)` then `ctx_search(queries)` — Fetch, chunk, index, query. Raw HTML never enters context.
5. **INDEX**: `ctx_index(content, source)` — Store content in FTS5 knowledge base for later search.

## Subagent routing

When spawning subagents (Agent/Task tool), the routing block is automatically injected into their prompt. Bash-type subagents are upgraded to general-purpose so they have access to MCP tools. You do NOT need to manually instruct subagents about context-mode.

## Output constraints

- Keep responses under 500 words.
- Write artifacts (code, configs, PRDs) to FILES — never return them as inline text. Return only: file path + 1-line description.
- When indexing content, use descriptive source labels so others can `ctx_search(source: "label")` later.

## ctx commands

| Command | Action |
|---------|--------|
| `ctx stats` | Call the `ctx_stats` MCP tool and display the full output verbatim |
| `ctx doctor` | Call the `ctx_doctor` MCP tool, run the returned shell command, display as checklist |
| `ctx upgrade` | Call the `ctx_upgrade` MCP tool, run the returned shell command, display as checklist |
