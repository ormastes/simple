# Gemini Agent — Self-Sufficient Feature Pipeline

**Full pipeline (ideal):** `/research` -> `/design` -> `/impl` -> `/verify` -> `/release`

Each step is **self-sufficient** — if prior steps were not done (by Claude, Codex, or anyone), do them yourself before proceeding.

## Cooperative Phase Dev

In multi-LLM cooperative mode, Gemini owns **Step 3 (UI/UX design)** — its primary strength:
```
Step 1: Claude /research  →  Step 2: Codex $research  →  Step 3: Gemini /design (UI)
→  Step 4: Codex $design (arch)  →  Step 5: Claude /design (quality)
```
See: `doc/07_guide/app/llm/llm_cooperative_dev_phase.md`

## Skills Reference

| Skill | File | Purpose |
|-------|------|---------|
| `/research` | `.gemini/commands/research.toml` | Local + domain research |
| `/sp_dev` | `.gemini/commands/sp_dev.toml` | Preferred full SPipe feature pipeline |
| `/design` | `.gemini/commands/design.toml` | UI/UX design (Step 3 primary) |
| `/impl` | `.gemini/commands/impl.toml` | 15-phase implementation |
| `/verify` | `.gemini/commands/verify.toml` | Production readiness check |
| `/release` | `.gemini/commands/release.toml` | Version bump + tag |
| `/ui_design` | `.gemini/commands/ui_design.toml` | TUI/GUI mockup creation |
| `/visual_test` | `.gemini/commands/visual_test.toml` | Visual regression testing |
| `/browser_research` | `.gemini/commands/browser_research.toml` | Chrome MCP domain research |
| `/stitch` | `.gemini/commands/stitch.toml` | Multi-file code generation |
| `/coding` | `.gemini/commands/coding.toml` | Simple language rules |

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

## Available Tools

| Tool | Purpose |
|------|---------|
| **Simple MCP** | `bin/simple query workspace-symbols`, `references`, `hover` — codebase search |
| **Simple LSP MCP** | `bin/simple query definition`, `completions` — code navigation |
| **Context7 MCP** | External library documentation lookup |
| **Chrome MCP** | Browser control for visual testing and web interaction |
| **Stitch MCP** | Multi-file code editing and generation |
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
bootstrap verifier inside FreeBSD. For manual VM debugging:

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
- Use Chrome MCP for visual reference gathering
- Output: `doc/01_research/domain/<feature>.md`

### Requirement Options
- Generate feature options with pros/cons/effort: `doc/02_requirements/feature/<feature>_options.md`
- Generate NFR options: `doc/02_requirements/nfr/<feature>_options.md`
- For broad lanes, record lower-model sidecars to use or merge (Codex Spark,
  Claude Haiku, Claude Sonnet), or mark `N/A`. Normal/highest-capability review
  must accept broad findings before options, exclusions, or done marks are trusted.
- **Ask user** to select, then write final: `doc/02_requirements/feature/<feature>.md` and `doc/02_requirements/nfr/<feature>.md`

---

## Step 2: Design

Check: `doc/04_architecture/<feature>.md` and `doc/05_design/<feature>.md` exist?

If missing, do all:

### UI Design (primary Gemini strength)
- TUI mockups with box-drawing characters, ANSI color annotations: `doc/05_design/<feature>_tui.md`
- GUI mockups with web patterns, responsive layout: `doc/05_design/<feature>_gui.md`
- Present component lists to user for confirmation

### Architecture
- Evaluate patterns, apply MDSOC where appropriate
- Output: `doc/04_architecture/<feature>.md`

### System Test Design
- SPipe BDD tests: `test/03_system/app/<app_name>/feature/<feature>_spec.spl`
- Generated/manual SPipe docs: `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md`
- Test plan: `doc/03_plan/sys_test/<feature>.md`
- Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Define shared interface names and manual-facing setup/checker helper names
  before implementation. Temporary helpers must fail explicitly with
  `assert(false)` or equivalent.
- Generate/read `doc/06_spec/...` as a scenario manual and revise steps,
  captures, inline/previous expansion, and visibility until primary flows are
  understandable without opening the source spec.

### Detail Design
- Data structures, algorithms, module interactions, error handling
- Output: `doc/05_design/<feature>.md`
- Agent task breakdown: `doc/03_plan/agent_tasks/<feature>.md`

---

## Step 3: Implementation

Implement in `src/**/<feature>.spl`:
1. Follow coding standards (`.spl` files only, generics with `<>`, no inheritance)
2. Unit + integration tests (80%+ coverage)
3. Doctest for public fns
4. Full test suite pass: `bin/simple test && bin/simple build lint`

---

## Step 4: Verify

Production readiness check:

| Check | Fail Condition |
|-------|---------------|
| SPipe Tests | `pass_todo`, `expect(true).to_equal(true)`, empty bodies |
| Implementation | Stub functions, hardcoded returns, TODO-only bodies |
| Requirements | REQ-NNN without implementation or test coverage |
| NFR | Targets without verification mechanism |
| Architecture | `doc/04_architecture/` missing or outdated |
| Design | `doc/05_design/` missing or outdated |

Must show `STATUS: PASS` before release.
Generated-manual quality and lower-model sidecar review must already be covered
by verify PASS; release must not repair or accept those gaps afterward.

Run:
```bash
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
```
New app leaf or `src/lib/gc_async_mut` env reads/process-run calls outside owner
modules must use env/process facades, not local `rt_env_get`, `rt_process_run`,
or `rt_process_run_timeout`.

---

## Step 5: Release

Version bump, CHANGELOG update, commit, tag, push.

---

## Extension Distribution

This repo is a registered Gemini CLI extension via `gemini-extension.json`.
- Users install: `gemini extensions install nicobailon/simple`
- Auto-discovered via `gemini-cli-extension` GitHub topic
- Guide: `doc/07_guide/tooling/ai_cli_registration.md`

---

## Critical Rules

- **Default tooling = pure-Simple self-hosted binary, not the Rust seed.** `test`/`lint`/`fmt`/`build`/`run`/MCP/LSP all run on `bin/release/<triple>/simple` (built via bootstrap). The seed (`src/compiler_rust/target/bootstrap/simple`) is bootstrap-only. If the self-hosted binary is slow/unstable, fix it in pure-Simple (`src/compiler`/`src/lib`/`src/app`) and re-deploy or file a bug — don't fall back to the seed. See `.claude/rules/bootstrap.md`
- **Self-sufficient**: never fail because another LLM didn't do its step — do it yourself
- NEVER overwrite another LLM's research — append and annotate
- All requirement options must include pros, cons, and effort estimate
- User MUST select requirements — never auto-select
- All code in `.spl` — no Python, no Bash (except 3 bootstrap scripts)
- SPipe matchers: built-in only (`to_equal`, `to_be`, `to_be_nil`, `to_contain`, etc.)
- Broad lanes must complete lower-model sidecars or mark `N/A`, then pass
  normal/highest-capability review before broad done marks or release PASS
- `doc/06_spec` must contain generated/manual Markdown and evidence assets only;
  executable `.spl` specs belong under `test/`
- For MCP, LSP, and tool-server work, design must review startup path, hot request paths, cache or index strategy, invalidation strategy, and startup/latency/RSS targets
- Production wrappers should execute cached compiled artifacts rather than raw source entrypoints
- Repeated full-tree scans, repeated rereads, shell-outs, and retry sleeps in hot request handlers require explicit design justification and verification evidence
- Verify perf-sensitive tooling with warm startup time, representative request latency, and max RSS on realistic fixtures

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
| 3 | Source code | `src/**/<feature>.spl` |
| 4 | Verify report | Terminal output (PASS/FAIL/WARN) |
