# LLM Cooperative Development Phases

A unified guide for developing features using Claude Code, Codex CLI, and Gemini CLI -- together or independently.

---

## Pipeline Overview

```
Phase 1: Research     →  Phase 2: Design     →  Phase 3: Impl     →  Phase 4: Verify  →  Phase 5: Release
  local + domain          arch + UI + tests       code + test           quality gate        version + tag
```

Every phase is **self-sufficient**. Any LLM can do any phase alone. If a prior phase was skipped, do it yourself before proceeding.

---

## Phase 1: Research

**Goal:** Understand the problem, explore the codebase, survey external knowledge, define requirements.

### Artifacts

| Artifact | Path |
|----------|------|
| Local research | `doc/01_research/local/<feature>.md` |
| Domain research | `doc/01_research/domain/<feature>.md` |
| Feature requirement options | `doc/02_requirements/feature/<feature>_options.md` |
| NFR options | `doc/02_requirements/nfr/<feature>_options.md` |
| Final feature requirements | `doc/02_requirements/feature/<feature>.md` |
| Final NFR requirements | `doc/02_requirements/nfr/<feature>.md` |

### Sub-Phases

**1.1 Local Research** -- search `src/` and `doc/` for related code, types, call chains, prior work.

**1.2 Domain Research** -- web search for external knowledge, papers, language design references, prior art.

**1.3 Requirement Options** -- generate multiple options with pros/cons/effort for user selection.

**1.4 User Decision** -- present options, user selects. Remove unchosen files, write final requirements.

### Tools by LLM

| Tool | Claude | Codex | Gemini |
|------|--------|-------|--------|
| Simple MCP (codebase query) | Yes | Yes | Yes |
| Simple LSP MCP (code nav) | Yes | Yes | Yes |
| Context7 MCP (library docs) | Yes | Yes | Yes |
| Web search | WebSearch tool | Playwright CLI | Playwright CLI, Chrome MCP |

### Skills / Commands

| LLM | Invocation |
|-----|-----------|
| Claude Code | `/research` (`.claude/skills/research.md`) |
| Codex CLI | `$research` (`.codex/skills/research/SKILL.md`) |
| Gemini CLI | `/research` (`.gemini/commands/research.toml`) |

### Multi-LLM Pattern (optional)

If multiple LLMs participate in research:
- Later LLMs **append and annotate** -- never overwrite prior research
- Validate prior findings against current `src/` state
- Identify gaps, add supplementary research

---

## Phase 2: Design

**Goal:** Create architecture, UI mockups, system tests, and detailed design.

### Prerequisites Check

| Artifact | Path | If missing |
|----------|------|-----------|
| Feature requirements | `doc/02_requirements/feature/<feature>.md` | Do Phase 1 first |
| NFR requirements | `doc/02_requirements/nfr/<feature>.md` | Do Phase 1 first |

### Artifacts

| Artifact | Path |
|----------|------|
| TUI design | `doc/05_design/<feature>_tui.md` |
| GUI design | `doc/05_design/<feature>_gui.md` |
| Architecture | `doc/04_architecture/<feature>.md` |
| System test plan | `doc/03_plan/sys_test/<feature>.md` |
| SSpec tests | `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl` |
| Detail design | `doc/05_design/<feature>.md` |
| Agent task breakdown | `doc/03_plan/agent_tasks/<feature>.md` |

### Sub-Phases

**2.1 UI Design** (if feature has UI)
- TUI: box-drawing characters, ANSI color annotations
- GUI: web patterns, responsive layout, wireframes
- Present component lists to user for confirmation

**2.2 Architecture**
- Evaluate patterns, apply MDSOC where appropriate
- Reference `src/compiler/85.mdsoc/` for MDSOC examples

**2.3 System Test Design**
- SSpec BDD tests with real assertions
- Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Every REQ-NNN must have at least one test

**2.4 Detail Design**
- Data structures, algorithms, module interactions, error handling
- Agent task breakdown for implementation

**2.5 Quality Check**
- Verify SSpec quality (target: A grade)
- Ask user: "Should architecture or design change?"

### Tools by LLM

| Tool | Claude | Codex | Gemini |
|------|--------|-------|--------|
| Simple MCP | Yes | Yes | Yes |
| Simple LSP MCP | Yes | Yes | Yes |
| Stitch MCP (multi-file edit) | -- | -- | Yes |
| Chrome MCP (visual ref) | -- | -- | Yes |

### Skills / Commands

| LLM | Invocation |
|-----|-----------|
| Claude Code | `/design` (`.claude/skills/design.md`) |
| Codex CLI | `$design` (`.codex/skills/design/SKILL.md`) |
| Gemini CLI | `/design` (`.gemini/commands/design.toml`) |

### LLM Strengths

| LLM | Design Strength |
|-----|----------------|
| **Claude** | Detail design, SSpec quality verification, requirement tracing |
| **Codex** | Architecture patterns, MDSOC, system test generation |
| **Gemini** | UI/UX design (TUI + GUI mockups), visual prototyping |

---

## Phase 3: Implementation

**Goal:** Write production code, tests, and documentation.

### Prerequisites Check

| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/feature/<feature>.md` | Do Phase 1 |
| Architecture | `doc/04_architecture/<feature>.md` | Do Phase 2 |
| Detail design | `doc/05_design/<feature>.md` | Do Phase 2 |
| System tests | `doc/06_spec/.../<feature>_spec.spl` | Do Phase 2 |

**If ALL exist**, skip directly to coding (Phase 3.4 below).

### Artifacts

| Artifact | Path |
|----------|------|
| Source code | `src/**/<feature>.spl` |
| Unit tests | `test/**/<feature>_spec.spl` |
| Bug limitations | `doc/08_tracking/bug/<feature>_limitations.md` |
| Completion report | `doc/09_report/<feature>_complete_<date>.md` |
| Guide (if needed) | `doc/07_guide/<feature>.md` |

### Sub-Phases (15-phase workflow in `/impl` skill)

**3.1-3.3** Research + Requirements -- skip if artifacts exist, otherwise do inline.

**3.4-3.5** Plan + Design -- skip if artifacts exist, otherwise do inline.

**3.6-3.7** System Test + Doc Consistency -- create `test/system/<feature>_spec.spl`, validate cross-references.

**3.8** Implementation -- write code in `src/**/<feature>.spl` following `/coding` rules.

**3.9-3.10** Unit + IT Tests (80%+ coverage) + Doctest for public fns.

**3.11-3.13** Bug Reports + Duplication Check + Refactoring (files >800 lines split).

**3.14** Full Test Suite: `bin/simple test && bin/simple build lint && bin/simple build check`

**3.15** Run `/verify` + VCS Sync.

### Skills / Commands

| LLM | Invocation |
|-----|-----------|
| Claude Code | `/impl` (`.claude/skills/impl.md`) |
| Codex CLI | `$impl` (`.codex/skills/impl/SKILL.md`) |
| Gemini CLI | `/impl` (`.gemini/commands/impl.toml`) |

### Critical Rules

- All code in `.spl` -- no Python, no Bash (except 3 bootstrap scripts)
- Generics: `<>` not `[]`
- No inheritance -- use composition, traits, mixins
- Stub Prevention: no `pass_todo` in final code (STUB001 = hard fail)
- `Result<T, E>` + `?` for error handling (no try/catch)

---

## Phase 4: Verify

**Goal:** Confirm implementation is production-level, not dummy/stub code.

### Artifacts

| Artifact | Path |
|----------|------|
| Verify report | Terminal output (PASS/FAIL/WARN summary table) |

### Checks (6 phases)

| Phase | What | Fail Condition |
|-------|------|---------------|
| **SSpec Tests** | Every `it` block has real assertions | `pass_todo`, `expect(true).to_equal(true)`, empty bodies |
| **Implementation** | All functions fully implemented | Stub functions, hardcoded returns, TODO-only bodies |
| **Feature Requirements** | Every REQ-NNN traced to code + test | Missing implementation or test coverage |
| **NFR** | Performance, reliability, security, observability | Targets without verification mechanism |
| **Architecture** | `doc/04_architecture/` updated | Missing or outdated arch docs, missing ADRs |
| **Design** | `doc/05_design/` updated | Missing design doc, no cross-references |

### Pass Criteria

- **Zero FAIL items** -- all stubs implemented, all REQs covered, all docs updated
- **WARN items reviewed** -- acceptable with justification, or converted to tracked TODOs
- Summary table must show `STATUS: PASS` before proceeding to release

### Skills / Commands

| LLM | Invocation |
|-----|-----------|
| Claude Code | `/verify` (`.claude/skills/verify.md`) |
| Codex CLI | `$verify` (`.codex/skills/verify/SKILL.md`) |
| Gemini CLI | `/verify` (`.gemini/commands/verify.toml`) |

---

## Phase 5: Release

**Goal:** Bump version, update changelog, commit, tag, push.

### Version Bump Options

| Argument | Effect | Example |
|----------|--------|---------|
| (none) or `patch`/`third` | Bump patch | 0.9.3 -> 0.9.4 |
| `minor`/`second` | Bump minor | 0.9.3 -> 0.10.0 |
| `major`/`first` | Bump major | 0.9.3 -> 1.0.0 |
| `X.Y.Z` | Set exact | 1.0.0 |

### Steps

1. Read current version from `simple.sdn`
2. Update 4 files: `simple.sdn`, `VERSION`, `main.spl`, `bootstrap_main.spl`
3. Update `CHANGELOG.md`
4. Commit: `jj commit -m "chore: release vX.Y.Z"`
5. Tag: `git tag -a vX.Y.Z -m "Release vX.Y.Z"`
6. **Ask before push** -- never push without user approval

### Skills / Commands

| LLM | Invocation |
|-----|-----------|
| Claude Code | `/release` (`.claude/skills/release.md`) |
| Codex CLI | `$release` (`.codex/skills/release/SKILL.md`) |
| Gemini CLI | `/release` (`.gemini/commands/release.toml`) |

---

## Tool Availability Matrix

### MCP Servers

| MCP Server | Claude | Codex | Gemini | Purpose |
|------------|--------|-------|--------|---------|
| **context7** | Yes | Yes | Yes | External library docs |
| **simple-mcp** | Yes | Yes | Yes | Codebase query (workspace-symbols, references, hover) |
| **simple-lsp-mcp** | Yes | Yes | Yes | Code navigation (definition, completions) |
| **chrome-devtools** | -- | Yes | Yes | Browser control, visual testing |
| **stitch-mcp** | -- | Yes | Yes | Multi-file code editing |
| **jj-git-mcp** | Yes | -- | -- | JJ/Git VCS operations |

### CLI Tools

| Tool | Claude | Codex | Gemini | Purpose |
|------|--------|-------|--------|---------|
| **Playwright CLI** | -- | Yes | Yes | Web scraping, browser automation, domain research |

### MCP Configuration Files

| LLM | Config File | Format |
|-----|------------|--------|
| Claude Code | `.claude/settings.local.json` | JSON |
| Codex CLI | `.codex/config.toml` | TOML `[mcp_servers]` |
| Gemini CLI | `.gemini/settings.json` | JSON `mcpServers` |

---

## Skill / Command File Locations

### Shared Pipeline Skills (all models, self-sufficient)

| Skill | Claude Code | Codex CLI | Gemini CLI |
|-------|-------------|-----------|------------|
| **research** | `.claude/skills/research.md` | `.codex/skills/research/SKILL.md` | `.gemini/commands/research.toml` |
| **design** | `.claude/skills/design.md` | `.codex/skills/design/SKILL.md` | `.gemini/commands/design.toml` |
| **impl** | `.claude/skills/impl.md` | `.codex/skills/impl/SKILL.md` | `.gemini/commands/impl.toml` |
| **verify** | `.claude/skills/verify.md` | `.codex/skills/verify/SKILL.md` | `.gemini/commands/verify.toml` |
| **release** | `.claude/skills/release.md` | `.codex/skills/release/SKILL.md` | `.gemini/commands/release.toml` |
| **coding** | `.claude/skills/coding.md` | `.codex/skills/coding/SKILL.md` | `.gemini/commands/coding.toml` |

### Model-Specific Skills (unique strengths)

**Claude Code** — Analysis & orchestration:

| Skill | File | Purpose |
|-------|------|---------|
| `/sspec` | `.claude/skills/sspec.md` | SSpec BDD framework |
| `/test` | `.claude/skills/test.md` | Test writing, container testing |
| `/debug` | `.claude/skills/debug.md` | Debugging, tracing |
| `/architecture` | `.claude/skills/architecture.md` | Compiler pipeline, modules |
| `/refactor` | `.claude/skills/refactor.md` | Code quality workflow |
| `/agents` | `.claude/skills/agents.md` | Multi-agent orchestration |
| `/doc` | `.claude/skills/doc.md` | 10 doc types |
| `/sync` | `.claude/skills/sync.md` | JJ VCS workflow |
| `/stdlib` | `.claude/skills/stdlib.md` | Stdlib development |
| `/sffi` | `.claude/skills/sffi.md` | FFI wrapper patterns |
| `/database` | `.claude/skills/database.md` | BugDB, TestDB, FeatureDB |
| `/mcp` | `.claude/skills/mcp.md` | MCP server implementation |
| `/deeplearning` | `.claude/skills/deeplearning.md` | ML pipeline operators |
| `/cuda` | `.claude/skills/cuda.md` | GPU/CUDA/SIMD |
| `/t32` | `.claude/skills/t32.md` | TRACE32 debugger |
| `/worktree` | `.claude/skills/worktree.md` | JJ workspace isolation |
| `/rule` | `.claude/skills/rule.md` | Engineering rules |

**Gemini CLI** — Visual & creative:

| Skill | File | Purpose |
|-------|------|---------|
| `/ui_design` | `.gemini/commands/ui_design.toml` | TUI/GUI mockup creation (primary) |
| `/visual_test` | `.gemini/commands/visual_test.toml` | Visual regression testing |
| `/browser_research` | `.gemini/commands/browser_research.toml` | Chrome MCP domain research |
| `/stitch` | `.gemini/commands/stitch.toml` | Multi-file code generation |

**Codex CLI** — Architecture & verification:

| Skill | File | Purpose |
|-------|------|---------|
| `$architecture` | `.codex/skills/architecture/SKILL.md` | MDSOC, ADR writing |
| `$mdsoc` | `.codex/skills/mdsoc-architecture-writing/SKILL.md` | MDSOC architecture docs |
| `$system_test` | `.codex/skills/system_test/SKILL.md` | SSpec system test design |

### Invocation Syntax

| LLM | Syntax | Example |
|-----|--------|---------|
| Claude Code | `/name` | `/verify` |
| Codex CLI | `$name` | `$verify` |
| Gemini CLI | `/name` | `/verify` |

---

## Instruction Files

| File | Read by | Purpose |
|------|---------|---------|
| `CLAUDE.md` | Claude (native), Codex (fallback), Gemini (fileName) | Primary project knowledge |
| `AGENTS.md` | Codex (native) | Codex pipeline + tools |
| `GEMINI.md` | Gemini (native) | Gemini pipeline + tools |

### Cross-Reading Configuration

| LLM | Native | Cross-reads | How |
|-----|--------|-------------|-----|
| Claude Code | `CLAUDE.md` | -- | -- |
| Codex CLI | `AGENTS.md` | `CLAUDE.md` | `project_doc_fallback_filenames` in `.codex/config.toml` |
| Gemini CLI | `GEMINI.md` | `CLAUDE.md` | `context.fileName` in `.gemini/settings.json` |

---

## Self-Sufficiency Principle

The core design principle: **every phase, every LLM, is self-sufficient.**

Before starting any phase, check if prerequisite artifacts exist:

| If you need... | Check for... | If missing... |
|----------------|-------------|---------------|
| Research | `doc/01_research/local/<feature>.md` | Do research yourself |
| Requirements | `doc/02_requirements/feature/<feature>.md` | Research + user selection |
| UI design | `doc/05_design/<feature>_tui.md` | Create mockups yourself |
| Architecture | `doc/04_architecture/<feature>.md` | Design it yourself |
| System tests | `doc/06_spec/.../<feature>_spec.spl` | Create SSpec tests yourself |
| Detail design | `doc/05_design/<feature>.md` | Create it yourself |
| Implementation | `src/**/<feature>.spl` | Implement it yourself |
| Verification | Verify report shows PASS | Run verify yourself |

**Common case:** User runs `/impl` with Claude, which does all phases 1-5 inline.

**Multi-LLM case:** Each LLM runs its phase, checks prior artifacts exist, extends them if present.

**Rule:** Never fail because another LLM didn't run. Never overwrite another LLM's work -- append and annotate.

---

## Artifact Directory Map

```
doc/
  01_research/
    local/<feature>.md            # Phase 1: local codebase research
    domain/<feature>.md           # Phase 1: external domain research
    general/                      # General research (not feature-specific)
  02_requirements/
    feature/<feature>.md          # Phase 1: final feature requirements
    feature/<feature>_options.md  # Phase 1: requirement options (deleted after selection)
    nfr/<feature>.md              # Phase 1: non-functional requirements
    nfr/<feature>_options.md      # Phase 1: NFR options (deleted after selection)
  03_plan/
    sys_test/<feature>.md         # Phase 2: system test plan
    agent_tasks/<feature>.md      # Phase 2: implementation task breakdown
  04_architecture/
    <feature>.md                  # Phase 2: architecture design
    adr/ADR-NNN-title.md          # Phase 2: architecture decision records
  05_design/
    <feature>.md                  # Phase 2: detail design
    <feature>_tui.md              # Phase 2: TUI mockups
    <feature>_gui.md              # Phase 2: GUI mockups
  06_spec/
    app/<app>/feature/<feature>_spec.spl  # Phase 2: SSpec system tests
  07_guide/
    <feature>.md                  # Phase 3: user guide (if needed)
  08_tracking/
    bug/<feature>_limitations.md  # Phase 3: known limitations
  09_report/
    <feature>_complete_<date>.md  # Phase 3: completion report
```

---

## Related Documents

- [AI CLI Coexistence Research](../01_research/general/ai_cli_coexistence_2026-03-28.md) -- full configuration mapping
- [Document Relationship Model](../FILE.md) -- PLAN -> REQ -> FEATURE -> TESTS hierarchy
- [Engineering Rules](../architecture/rule/README.md) -- coding, testing, documentation policies
