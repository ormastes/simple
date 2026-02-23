# doc/ Directory - Documentation Hub

**Purpose:** Comprehensive project documentation (2,000+ files)
**Organization:** 36 subdirectories by topic and document type
**Formats:** Markdown (.md), SDN (.sdn), reports, specifications

---

## 📋 Quick Navigation

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
| **architecture/** | System design | Overall structure |
| **adr/** | Architecture Decision Records | Why key decisions were made |
| **research/** | Research and option analysis | What should we choose and why |
| **rule/** | Engineering rules | How engineers must work |
| **api/** | API documentation | Function references |

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
- `syntax_quick_reference.md` - Complete syntax reference
- `getting_started.md` - First steps
- `container_testing.md` - Docker testing guide
- `folder_file.md` - Project organization
- `documentation_coverage.md` - Doc coverage system
- `i18n.md` - Internationalization

**Use case:** Learning Simple language and tooling

---

### spec/ (Formal Specifications)
**Audience:** Language implementers

**Contents:**
- `tooling/` - Tool specifications
- `language/` - Language grammar
- `stdlib/` - Standard library specs
- `mcp/` - MCP protocol specs

**Use case:** Understanding formal language definition

---

### report/ (Implementation Reports)
**Audience:** Developers tracking progress

**Contents:**
- **Completion reports:** `*_complete_*.md` - Finished features
- **Session reports:** `*_session_*.md` - Work sessions
- **Status reports:** `*_status_*.md` - Current state
- **Analysis reports:** `*_analysis_*.md` - Code analysis

**Recent highlights:**
- `bin_cleanup_complete_2026-02-16.md` - bin/ reorganization
- `examples_reorganization_complete_2026-02-16.md` - examples/ restructure
- `test_runner_fixes_2026-02-14.md` - Test runner improvements

**Use case:** Understanding what's been implemented and how

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
- Refactoring plans
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

---

### tutorial/ (Step-by-Step Tutorials)
Interactive learning materials:
- Language tutorials
- Tool usage tutorials
- Example walkthroughs

---

### examples/ (Example Documentation)
Documentation about examples:
- Example organization
- How to run examples
- Example categories

---

### feature/ (Feature Specifications)
BDD-style feature documents bridging requirements and tests:
- `feature.md` - Feature list (auto-generated by test runner)
- `pending_feature.md` - Upcoming features (auto-generated)
- Feature specification docs: user-facing scenarios derived from REQ-NNN
- See [feature/README.md](feature/README.md) for template and format

---

### test/ (Test Documentation)
Testing documentation:
- `test_result.md` - Test results (auto-generated)
- `llm_integration_testing.md` - LLM testing guide
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

### integration/ (Integration Guides)
External integrations:
- Claude Code MCP integration
- IDE integrations
- CI/CD setup

---

### runtime/ (Runtime Documentation)
Runtime system:
- Interpreter documentation
- JIT compiler docs
- Memory management

---

### compiler/ (Compiler Documentation)
Compiler implementation:
- Frontend (lexer, parser)
- Middle-end (HIR, MIR)
- Backend (code generation)

---

### backend/ (Backend Documentation)
Code generation backends:
- Native compilation
- Cranelift backend
- LLVM backend
- Interpreter backend

---

### format/ (Format Specifications)
Data formats:
- SDN (Simple Data Notation)
- SMF (Simple Module Format)
- Binary formats

---

### refactoring/ (Refactoring Docs)
Code refactoring:
- Refactoring plans
- Migration guides
- Cleanup reports

---

### migration/ (Migration Guides)
Migration documentation:
- Language migration guides
- Tool migration
- Breaking changes

---

### workflow/ (Development Workflows)
Process documentation:
- Development workflow
- Release workflow
- Testing workflow

---

### session/ (Development Sessions)
Session notes:
- Pair programming sessions
- Design sessions
- Planning sessions

---

### progress/ (Progress Tracking)
Project progress:
- Milestone tracking
- Feature completion
- Roadmap status

---

### task/ (Task Documentation)
Task system:
- Task definitions
- Task execution
- Task results

---

### todo/ (TODO Tracking)
TODO items:
- TODO list
- FIXME tracking
- Future improvements

---

### coverage/ (Coverage Reports)
Test coverage:
- Code coverage reports
- Documentation coverage
- Feature coverage

---

### dashboard/ (Project Dashboards)
Visual project status:
- Build dashboard
- Test dashboard
- Coverage dashboard

---

### analysis/ (Code Analysis)
Static analysis:
- Code quality reports
- Complexity analysis
- Dependency analysis

---

### knowhow/ (Knowledge Base)
Institutional knowledge:
- `KNOWHOW.md` - Important learnings
- Tips and tricks
- Common pitfalls

---

### requirement/ (Functional Requirements)
System-level capability requirements with user context:
- User request (verbatim or close paraphrase)
- Engineering interpretation of the request
- Formal REQ-NNN statements (what the system *shall* do)
- Cross-references to plan, design, feature, NFR docs
- See [requirement/README.md](requirement/README.md) for template

### nfr/ (Non-Functional Requirements / SLO)
Measurable quality constraints:
- Performance targets (latency, throughput)
- Reliability SLOs (uptime, error rate)
- Security requirements (token expiry, crypto standards)
- Observability requirements (logging, tracing)
- See [nfr/README.md](nfr/README.md) for template

### adr/ (Architecture Decision Records)
Formal records of significant architectural decisions:
- Context: why the decision was needed
- Decision: what was chosen
- Alternatives considered
- Consequences (positive and negative)
- See [adr/README.md](adr/README.md) for template and lifecycle

### rule/ (Engineering Rules)
Mandatory engineering, architectural, testing, and operational rules:
- Architecture rules (dependency direction, layer responsibilities)
- Coding standards (language rules, error handling, naming)
- Testing policy (coverage, BDD requirements)
- Documentation policy (spec file requirements, ADR process)
- Security, performance, and operational rules
- See [rule/README.md](rule/README.md) for full rules

### research/ (Research Documents)
Research and exploration:
- Language research
- Performance research
- Algorithm exploration
- Options analysis before design decisions

---

### implementation/ (Implementation Details)
Low-level implementation:
- Data structures
- Algorithms
- Optimizations

---

### archive/ (Archived Documentation)
Historical documents:
- Deprecated features
- Old designs
- Legacy documentation

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
| `TODO.md` | `bin/simple todo-scan` | On demand |

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
# Recent reports
ls -lt doc/report/ | head -20

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
1. **Refactoring plan:** `doc/plan/refactoring_name_YYYY-MM-DD.md`
2. **Progress tracking:** Update plan with status
3. **Completion report:** `doc/report/refactoring_complete_YYYY-MM-DD.md`

---

## 📈 Documentation Statistics

**Total files:** 2,000+
**Categories:** 36 subdirectories
**Auto-generated:** 5 files (updated automatically)
**User guides:** 50+ guides
**Reports:** 500+ implementation reports
**Design docs:** 200+ design documents

---

## 🎯 Common Use Cases

### "I want to learn Simple"
→ Start with `doc/guide/getting_started.md`
→ Then `doc/guide/syntax_quick_reference.md`
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
2. `guide/syntax_quick_reference.md` - Language reference
3. `contributing/` - How to contribute
4. `guide/container_testing.md` - Testing guide

### Must-Read for Users
1. `guide/getting_started.md` - First steps
2. `guide/syntax_quick_reference.md` - Syntax reference
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
- Archive old reports to `doc/archive/`
- Update outdated guides
- Review auto-generated docs
- Check for broken links

### Per Release
- Update version numbers in docs
- Generate release notes
- Archive previous version docs
- Update tutorials for changes

---

**Last Updated:** 2026-02-16
**Maintainer:** Documentation Team
**Size:** ~50MB (mostly Markdown)
**Index:** [INDEX.md](INDEX.md) - Complete file listing
