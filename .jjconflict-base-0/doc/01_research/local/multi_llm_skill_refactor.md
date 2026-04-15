# Multi-LLM Skill Refactor — Research Plan

**Date:** 2026-03-28
**Status:** Implementation
**Feature:** Per-model skill ownership + cooperative phase dev preservation

---

## 1. Problem Statement

The current multi-LLM setup has three AI CLIs (Claude Code, Gemini CLI, Codex CLI) sharing a cooperative dev pipeline, but:
- Skills are not clearly owned by specific models
- Trigger words are inconsistent across models (Claude `/`, Gemini `/`, Codex `$`)
- Each model lacks model-specific skills that leverage its strengths
- The cooperative phase dev pipeline exists in docs but isn't reflected in skill structure
- No clear separation between "solo mode" (one LLM alone) and "cooperative mode" (phased handoff)

---

## 2. Current State

### 2.1 Skill Inventory

| Location | Model | Count | Trigger | Format |
|----------|-------|-------|---------|--------|
| `.claude/skills/*.md` | Claude Code | 16 | `/skill` | Markdown |
| `.gemini/commands/*.toml` | Gemini CLI | 5 | `/command` | TOML |
| `.codex/skills/*/SKILL.md` | Codex CLI | 1 | `$skill` | Markdown in subdirs |
| `.agents/skills/*/SKILL.md` | Agent teams | 5 | N/A | Markdown in subdirs |

### 2.2 Cooperative Pipeline (5-Step)

```
Step 1: research_claude  (Claude)  — Local + domain research, MCP+LSP agents
Step 2: research_codex   (Codex)   — Forked parallel research, requirement selection
Step 3: design_gemini    (Gemini)  — UI/UX design (TUI + GUI mockups)
Step 4: design_codex     (Codex)   — Architecture + system test design
Step 5: design_claude    (Claude)  — SSpec quality + detail design refinement
```

### 2.3 Model Strengths

| Model | Strengths |
|-------|-----------|
| **Claude Code** | Deep code analysis, agent orchestration, SSpec quality, complex impl, debugging |
| **Gemini CLI** | UI/UX design, visual prototyping, browser automation, creative mockups |
| **Codex CLI** | Architecture patterns, MDSOC, verification, parallel forked research |

---

## 3. Requirements

### REQ-1: Preserve Cooperative Phase Dev
The 5-step cooperative pipeline must remain intact. Each model can participate in its assigned steps.

### REQ-2: Per-Model Skill Sets
Each model gets its own skill set that leverages its strengths. Skills are organized by model ownership.

### REQ-3: Solo Mode Support
Each model must be self-sufficient — it can run the full pipeline alone (research → design → impl → verify → release).

### REQ-4: Different Trigger Words
- Claude Code: `/skill` (slash commands via `.claude/skills/`)
- Gemini CLI: `/command` (slash commands via `.gemini/commands/`)
- Codex CLI: `$skill` (dollar-prefix via `.codex/skills/`)

### REQ-5: Deploy 3 Instances
Each model's config directory is a complete, deployable instance:
- `.claude/` — Plugin for Claude Code
- `.gemini/` — Extension for Gemini CLI
- `.codex/` — MCP-supported config for Codex CLI

---

## 4. Design — Skill Distribution

### 4.1 Shared Skills (all models get their own version)

Every model needs these for self-sufficiency in solo mode:

| Skill | Claude | Gemini | Codex |
|-------|--------|--------|-------|
| research | `/research` | `/research` | `$research` |
| design | `/design` | `/design` | `$design` |
| impl | `/impl` | `/impl` | `$impl` |
| verify | `/verify` | `/verify` | `$verify` |
| release | `/release` | `/release` | `$release` |

### 4.2 Model-Specific Skills (unique strengths)

**Claude Code** — Analysis & orchestration:

| Skill | Purpose |
|-------|---------|
| `/coding` | Simple language rules, syntax, runtime limits |
| `/sspec` | SSpec BDD framework — matchers, hooks, structure |
| `/test` | Test writing, methodology, container testing |
| `/debug` | Debugging, tracing, fault detection |
| `/architecture` | Compiler pipeline, module structure |
| `/refactor` | Code quality refactoring workflow |
| `/agents` | Agent loop iteration, multi-agent orchestration |
| `/doc` | Documentation writing (10 doc types) |
| `/sync` | Jujutsu VCS workflow |
| `/stdlib` | Stdlib module development |
| `/sffi` | FFI wrapper patterns |
| `/database` | BugDB, TestDB, FeatureDB |
| `/mcp` | MCP server implementation |
| `/deeplearning` | ML pipeline operators |
| `/cuda` | GPU/CUDA/SIMD programming |
| `/t32` | TRACE32 debugger setup |
| `/worktree` | JJ workspace isolation |
| `/rule` | Engineering rules, ADR process |

**Gemini CLI** — Visual & creative:

| Skill | Purpose |
|-------|---------|
| `/ui_design` | TUI/GUI mockup creation (primary strength) |
| `/visual_test` | Visual regression testing, screenshot comparison |
| `/browser_research` | Chrome MCP + Playwright domain research |
| `/stitch` | Multi-file code generation with Stitch MCP |
| `/coding` | Simple language rules (shared subset) |

**Codex CLI** — Architecture & verification:

| Skill | Purpose |
|-------|---------|
| `$architecture` | Architecture patterns, MDSOC evaluation |
| `$mdsoc` | MDSOC-specific architecture writing |
| `$system_test` | System test design and BDD generation |
| `$coding` | Simple language rules (shared subset) |

### 4.3 Cooperative Phase Mapping

```
COOPERATIVE MODE (multi-LLM phased dev):
  Phase 1 Research:  Claude /research  →  Codex $research  →  (merged requirements)
  Phase 2 Design:    Gemini /design (UI)  →  Codex $design (arch)  →  Claude /design (quality)
  Phase 3 Impl:      Claude /impl (primary) or any model
  Phase 4 Verify:    Codex $verify (primary)  →  Claude /verify (secondary)
  Phase 5 Release:   Any model

SOLO MODE (single LLM):
  Claude:  /research → /design → /impl → /verify → /release
  Gemini:  /research → /design → /impl → /verify → /release
  Codex:   $research → $design → $impl → $verify → $release
```

---

## 5. Implementation Plan

### Phase 1: Refactor Claude Skills (`.claude/skills/`)
- Keep all 16 existing skills + add cooperative phase annotations
- Add `coop_phase` header to research.md and design.md indicating their step in cooperative pipeline
- Ensure `/impl` is self-sufficient with all 15 phases

### Phase 2: Refactor Gemini Extension (`.gemini/`)
- Expand 5 commands to include model-specific skills (ui_design, visual_test, browser_research, stitch)
- Add cooperative phase annotations to design command (Step 3: UI/UX primary)
- Add `coding.toml` with Simple language subset rules

### Phase 3: Refactor Codex MCP (`.codex/skills/`)
- Expand from 1 skill to full set: research, design, impl, verify, release, architecture, mdsoc, system_test, coding
- Add cooperative phase annotations (Step 2: research, Step 4: architecture)
- Each skill in its own subdirectory with SKILL.md

### Phase 4: Update Cooperative Dev Guide
- Update `doc/guide/llm_cooperative_dev_phase.md` with new skill names
- Update CLAUDE.md, AGENTS.md, GEMINI.md to reference refactored skills
- Ensure `.agents/skills/` aligns with new structure

### Phase 5: Deploy & Verify
- Verify each model's config is a complete deployable instance
- Verify self-sufficiency in solo mode
- Verify cooperative handoff works

---

## 6. File Changes Summary

### New Files
- `.gemini/commands/ui_design.toml` — Gemini UI design skill
- `.gemini/commands/visual_test.toml` — Visual testing skill
- `.gemini/commands/browser_research.toml` — Browser-based research
- `.gemini/commands/stitch.toml` — Multi-file generation
- `.gemini/commands/coding.toml` — Simple language rules
- `.codex/skills/research/SKILL.md` — Codex research skill
- `.codex/skills/design/SKILL.md` — Codex design skill
- `.codex/skills/impl/SKILL.md` — Codex impl skill
- `.codex/skills/verify/SKILL.md` — Codex verify skill
- `.codex/skills/release/SKILL.md` — Codex release skill
- `.codex/skills/architecture/SKILL.md` — Architecture patterns
- `.codex/skills/system_test/SKILL.md` — System test design
- `.codex/skills/coding/SKILL.md` — Simple language rules

### Modified Files
- `.claude/skills/research.md` — Add cooperative phase annotation
- `.claude/skills/design.md` — Add cooperative phase annotation
- `doc/guide/llm_cooperative_dev_phase.md` — Updated skill references
- `CLAUDE.md` — Updated skills table
- `AGENTS.md` — Updated with Codex skills
- `GEMINI.md` — Updated with Gemini skills

---

## 7. Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Skill duplication across models | Shared content in `doc/guide/llm_cooperative_dev_phase.md`, model-specific skills reference it |
| Trigger word confusion | Clear documentation in each model's instruction file |
| Breaking existing workflows | All changes are additive — existing skills preserved |
| MCP server compatibility | All 3 models share same MCP servers (simple-mcp, simple-lsp-mcp, context7) |
