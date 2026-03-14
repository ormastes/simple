# doc/ Directory - Documentation Hub

**Purpose:** Comprehensive project documentation
**Quick Start:** See [README.md](README.md) for entry points
**Glossary:** See [architecture/glossary.md](architecture/glossary.md) for key concepts

---

## I want to...

| Goal | Document |
|------|----------|
| Learn Simple language | [guide/README.md](guide/README.md) |
| Syntax cheatsheet | [guide/quick_reference/syntax_quick_reference.md](guide/quick_reference/syntax_quick_reference.md) |
| Async programming | [guide/sync_async/async/async_guide.md](guide/sync_async/async/async_guide.md) |
| Set up my editor (LSP) | [guide/lsp_integration.md](guide/lsp_integration.md) |
| Compiler backends | [guide/backend/capabilities.md](guide/backend/capabilities.md) |
| Understand architecture | [architecture/overview.md](architecture/overview.md) |
| Codebase inventory | [architecture/file_class_structure.md](architecture/file_class_structure.md) |
| See what features work | [feature/FEATURES_THAT_WORK.md](feature/FEATURES_THAT_WORK.md) |
| Feature status | [feature/needed_feature.md](feature/needed_feature.md) |
| Deploy to production | [release/PRODUCTION_READINESS.md](release/PRODUCTION_READINESS.md) |
| Test results | [test/test_result.md](test/test_result.md) |

---

## Quick Navigation

| Category | Purpose | Key Files |
|----------|---------|-----------|
| **guide/** | User guides & tutorials | Start here for learning |
| **spec/** | Language specifications | Formal grammar, semantics |
| **report/** | Implementation reports | What's been done |
| **design/** | Design documents | How features work |
| **plan/** | Planning documents | Why, scope, milestones, risks |
| **requirement/** | Functional requirements | User request + interpretation + REQ-NNN |
| **feature/** | Feature specifications (BDD) | How user experiences the requirement |
| **nfr/** | Non-functional requirements / SLOs | Performance, reliability, security |
| **architecture/** | System design, glossary | Overall structure |
| **adr/** | Architecture Decision Records | Why key decisions were made |
| **research/** | Research, option analysis, code analysis | What should we choose and why |
| **rule/** | Engineering rules | How engineers must work |
| **api/** | API documentation | Function references |
| **format/** | Format specifications | SDN, SMF, binary formats |

---

## 🗺️ Document Relationship Model

```
PLAN (doc/plan/)
  ↓
REQUIREMENTS (doc/requirement/)
  ↓                   ↘
FEATURE (doc/feature/)  NFR (doc/nfr/)
  ↓
BDD TESTS (*_spec.spl)
  ↓
TEST RESULTS (doc/test/)

Parallel flows:
RESEARCH (doc/research/) → DESIGN (doc/design/) → ADR (doc/adr/)
REQUIREMENTS → ARCHITECTURE (doc/architecture/)
GUIDES (doc/guide/) ← OPERATIONS + RUNBOOKS
RULES (doc/rule/) ← enforced via CI + review
```

| Doc Type | Answers |
|----------|---------|
| **Plan** | What and when |
| **Requirement** | What must the system do |
| **Feature** | How the user experiences the requirement |
| **NFR / SLO** | How well must it work |
| **Design / Architecture** | How it is built |
| **ADR** | Why this decision was made |
| **Research** | What should we choose and why |
| **Guide / Rule** | How to use or operate; how engineers must work |

---

## 📚 Primary Documentation Categories

### guide/ (User Guides)
**Audience:** Users learning Simple

**Key guides:**
- `quick_reference/syntax_quick_reference.md` - Complete syntax reference
- `getting_started.md` - First steps
- `container_testing.md` - Docker testing guide
- `folder_file.md` - Project organization
- `documentation_coverage.md` - Doc coverage system
- `tooling/` - Tool guides (merged from former `tools/`)
- `i18n.md` - Internationalization

**Use case:** Learning Simple language and tooling

**Note:** Writing guides moved to `contributing/writing/`.

---

### spec/ (Formal Specifications)
**Audience:** Language implementers

**Contents:**
- `tooling/` - Tool specifications
- `language/` - Language grammar and generated specs (merged from former `generated/`)
- `stdlib/` - Standard library specs
- `mcp/` - MCP protocol specs

**Use case:** Understanding formal language definition

---

### report/ (Implementation Reports)
**Audience:** Developers tracking progress

**Contents:** Recent reports only (~9 files); older reports archived to `archive/report/`.
- **Completion reports:** `*_complete_*.md` - Finished features
- **Status reports:** `*_status_*.md` - Current state

**Recent highlights:**
- `mcp_json_fix_2026-03-02.md` - MCP JSON fix
- `compiler_mdsoc_migration.md` - Compiler MDSOC numbered layer migration
- `compiler_mdsoc_impl_plan.md` - MDSOC implementation plan

**Use case:** Understanding what's been implemented recently

---

### design/ (Design Documents)
**Audience:** Developers understanding architecture

**Contents:**
- Feature design documents
- System architecture designs
- Implementation plans
- Trade-off analyses

**Key documents:**
- `diagnostics_*.md` - Diagnostic system design
- `i18n_*.md` - Internationalization design
- `linker_script_gen_design.md` - Linker generation

**Use case:** Understanding design decisions

---

### plan/ (Planning Documents)
**Audience:** Project planners

**Contents:**
- Feature roadmaps
- Migration plans
- Refactoring plans (merged from former top-level `refactoring/` into `plan/refactoring/`)
- Cleanup plans

**Recent:**
- `examples_reorganization_2026-02-16.md`
- `bin_cleanup_2026-02-16.md`
- `directory_restructure_migration_2026-01-21.md`

**Use case:** Planning future work

---

### architecture/ (System Architecture)
**Audience:** Developers understanding structure

**Key files:**
- `file_class_structure.md` - Complete codebase inventory
- `compiler_pipeline.md` - Compilation stages
- `module_system.md` - Module organization
- `self_hosting.md` - Bootstrap process

**Use case:** Understanding overall system design

---

### api/ (API Documentation)
**Audience:** Developers using APIs

**Contents:**
- Function references
- Class documentation
- Module interfaces
- FFI bindings

**Use case:** API reference lookup

---

## 🗂️ Supporting Categories

### contributing/ (Contribution Guides)
How to contribute to Simple project:
- Code style guidelines
- Pull request process
- I18n translation guide
- Testing requirements
- `writing/` - Writing guides (merged from former `guide/writing/`)

---

### feature/ (Feature Specifications)
BDD-style feature documents bridging requirements and tests:
- `feature.md` - Feature list (auto-generated by test runner)
- `pending_feature.md` - Upcoming features (auto-generated)
- `FEATURES_THAT_WORK.md` - Working features overview
- `needed_feature.md` - Feature status and gaps
- Feature specification docs: user-facing scenarios derived from REQ-NNN
- See [feature/README.md](feature/README.md) for template and format

**Note:** Former `usage/` and `category/` subdirs moved to `archive/feature_usage/` and `archive/feature_category/`.

---

### test/ (Test Documentation)
Testing documentation:
- `test_result.md` - Test results (auto-generated)
- `llm_integration_testing.md` - LLM testing guide
- `coverage/` - Test coverage reports (merged from former top-level `coverage/`)
- Test methodology

---

### bug/ (Bug Documentation)
Bug tracking:
- `bug_report.md` - Bug list (auto-generated)
- Known issues
- Bug analysis

---

### build/ (Build Documentation)
Build system docs:
- `recent_build.md` - Build status (auto-generated)
- Build process
- Bootstrap documentation

---

### release/ (Release Documentation)
Release process:
- Release checklists
- Version history
- Release notes

---

### format/ (Format Specifications)
- SDN (Simple Data Notation), SMF (Simple Module Format)

---

### Other Directories

| Directory | Purpose |
|-----------|---------|
| **progress/** | Milestone tracking and feature completion |
| **archive/** | Historical/deprecated documentation (see below) |
| **contributing/** | Contribution guides (i18n translations, writing guides) |
| **adr/** | Architecture Decision Records — see [adr/README.md](adr/README.md) |
| **requirement/** | Functional requirements — see [requirement/README.md](requirement/README.md) |
| **nfr/** | Non-functional requirements / SLOs — see [nfr/README.md](nfr/README.md) |
| **rule/** | Engineering rules — see [rule/README.md](rule/README.md) |

#### archive/ Contents

The `archive/` directory contains documentation that has been superseded, completed, or is no longer actively maintained:

| Subdirectory | Originally From |
|--------------|-----------------|
| **session/** | Former top-level `session/` — development session notes |
| **dashboard/** | Former top-level `dashboard/` — SDN project dashboards |
| **task/** | Former top-level `task/` — task tracking system |
| **todo/** | Former top-level `todo/` — TODO groupings and investigation notes |
| **report/** | Older reports from `report/` (recent reports remain in `report/`) |
| **feature_usage/** | Former `feature/usage/` — feature usage documentation |
| **feature_category/** | Former `feature/category/` — feature categorization |

---

## 📊 Auto-Generated Documentation

These files are automatically updated by the build system:

| File | Generated By | Frequency |
|------|--------------|-----------|
| `feature/feature.md` | Test runner | Every test run |
| `feature/pending_feature.md` | Test runner | Every test run |
| `test/test_result.md` | Test runner | Every test run |
| `build/recent_build.md` | Build system | Every build |
| `bug/bug_report.md` | `bin/simple bug-gen` | On demand |

**Don't edit these files manually!** They will be overwritten.

---

## 📝 Documentation Standards

### Markdown Format
All documentation uses GitHub-flavored Markdown:
- Headers: `#`, `##`, `###`
- Code blocks: ` ```language `
- Lists: `-`, `*`, `1.`
- Tables: Pipe-delimited
- Links: `[text](url)`

### File Naming
- Use lowercase with underscores: `feature_name.md`
- Date suffix for reports: `*_2026-02-16.md`
- Descriptive names: `diagnostics_i18n_complete.md` not `doc1.md`

### Document Structure
```markdown
# Title

**Date:** YYYY-MM-DD (for reports)
**Status:** Complete/In Progress/Planned
**Purpose:** Brief description

## Summary (if report)

## Sections...

---

**Last Updated:** YYYY-MM-DD
```

---

## 🔍 Finding Documentation

### By Topic
```bash
# Find docs about a topic
grep -r "diagnostic" doc/ --include="*.md"

# Find in specific category
ls doc/guide/*diagnostic*
```

### By Date
```bash
# Recent reports (only ~9 active files; older in archive/report/)
ls -lt doc/report/

# Recent plans
ls -lt doc/plan/ | head -10
```

### By Status
```bash
# Completed features
grep -l "Status.*Complete" doc/report/*.md

# In-progress work
grep -l "Status.*In Progress" doc/design/*.md
```

---

## ✍️ Writing Documentation

### For New Features
1. **Plan:** `doc/plan/feature_name.md` — why, scope, milestones, risks
2. **Requirements:** `doc/requirement/feature_name.md` — user request + REQ-NNN statements
3. **Feature spec:** `doc/feature/feature_name.md` — BDD scenarios from requirements
4. **NFR:** `doc/nfr/feature_name.md` — performance, reliability, security targets
5. **Research:** `doc/research/feature_name.md` — options analysis (if non-obvious)
6. **Design:** `doc/design/feature_name.md` — internal structure and decisions
7. **ADR:** `doc/adr/ADR-NNN-title.md` — for major architectural decisions made during design
8. **BDD tests:** `test/*_spec.spl` — link back to `**Requirements:**` + `**Design:**` in docstring
9. **Completion report:** `doc/report/feature_complete_YYYY-MM-DD.md`
10. **User guide:** `doc/guide/feature_usage.md` (if user-facing)

### For Bug Fixes
1. **Bug analysis:** `doc/bug/bug_analysis_YYYY-MM-DD.md`
2. **Fix report:** `doc/report/bug_fix_YYYY-MM-DD.md`

### For Refactoring
1. **Refactoring plan:** `doc/plan/refactoring/refactoring_name_YYYY-MM-DD.md`
2. **Progress tracking:** Update plan with status
3. **Completion report:** `doc/report/refactoring_complete_YYYY-MM-DD.md`

---

## Documentation Statistics

**Total doc files:** 3,462 .md
**Categories:** 36 subdirectories
**Auto-generated:** 5 files (updated automatically)
**User guides:** 50+ guides
**Reports:** ~9 recent reports (older reports in `archive/report/`)
**Design docs:** 200+ design documents

### Project-Wide Statistics (2026-03-02)
- **Source files:** 3,708 .spl + 1,801 .rs = 5,509 total
- **Test files:** 1,772 .spl
- **Lines of code:** ~780K .spl, ~2.86M .rs
- **Total tracked files:** ~27,926
- **Self-hosting:** Stage 3-4 COMPLETE (fixed-point reached 2026-02-28)

### Notable Changes Since 2026-02-16
- **Compiler MDSOC migration:** `src/compiler/` now uses numbered layers (00.common through 99.loader)
- **Deleted .disabled libraries:** godot, graphics, ml, ui, units, unreal, web, browser, electron, coverage, doctest, parser, spec/assertions, spec/bdd (cleaned from `src/compiler_rust/lib/std/src/`)
- **New app:** `src/app/yank/` (yank tool)
- **MCP handler adapters** relocated: `src/lib/nogc_sync_mut/mcp/handler_adapters/` -> `src/lib/nogc_async_mut/mcp/handler_adapters/` (debug_adapter, debug_log_adapter, diag_adapter)
- **New compiler module:** `src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl` (string builder optimization pass)
- **New test daemon:** `src/app/test_daemon/manifest_daemon.spl`

---

## 🎯 Common Use Cases

### "I want to learn Simple"
→ Start with `doc/guide/getting_started.md`
→ Then `doc/guide/quick_reference/syntax_quick_reference.md`
→ Try `examples/01_getting_started/`

### "I want to understand how feature X works"
→ Check `doc/design/feature_x*.md`
→ Read `doc/report/feature_x_complete*.md`
→ Look at implementation in `src/`

### "I want to contribute"
→ Read `doc/contributing/`
→ Check `doc/plan/` for planned work
→ See `doc/architecture/` for system overview

### "I want to integrate with Simple"
→ Check `doc/integration/`
→ See `doc/api/` for API docs
→ Read relevant specs in `doc/spec/`

---

## 🔗 Related Directories

- **examples/** - Code examples (see examples/FILE.md)
- **test/** - Test suites
- **src/** - Implementation (the docs document this!)
- **.claude/skills/** - Skill documentation

---

## 📚 Key Documents by Category

### Must-Read for Developers
1. `architecture/file_class_structure.md` - Codebase overview
2. `guide/quick_reference/syntax_quick_reference.md` - Language reference
3. `contributing/` - How to contribute
4. `guide/container_testing.md` - Testing guide

### Must-Read for Users
1. `guide/getting_started.md` - First steps
2. `guide/quick_reference/syntax_quick_reference.md` - Syntax reference
3. `tutorial/` - Interactive tutorials
4. `examples/` - Code examples

### Must-Read for Integrators
1. `integration/` - Integration guides
2. `api/` - API documentation
3. `spec/` - Formal specifications
4. `format/` - Data formats

---

## 🛠️ Maintenance

### Monthly Tasks
- Archive old reports to `doc/archive/report/`
- Update outdated guides
- Review auto-generated docs
- Check for broken links

### Per Release
- Update version numbers in docs
- Generate release notes
- Archive previous version docs
- Update tutorials for changes

---

**Last Updated:** 2026-03-14
**Maintainer:** Documentation Team
**Size:** 3,462 .md files
**Index:** This file (`FILE.md`) is the complete documentation hub
