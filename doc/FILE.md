# doc/ Directory - Documentation Hub

**Purpose:** Comprehensive project documentation (numbered folder structure)
**Quick Start:** See [README.md](README.md) for entry points
**Glossary:** See [04_architecture/glossary.md](04_architecture/glossary.md) for key concepts

---

## I want to...

| Goal | Document |
|------|----------|
| Learn Simple language | [07_guide/README.md](07_guide/README.md) |
| Syntax cheatsheet | [07_guide/quick_reference/syntax_quick_reference.md](07_guide/quick_reference/syntax_quick_reference.md) |
| Understand architecture | [04_architecture/overview.md](04_architecture/overview.md) |
| Codebase inventory | [04_architecture/file_class_structure.md](04_architecture/file_class_structure.md) |
| See what features work | [02_requirements/feature/FEATURES_THAT_WORK.md](02_requirements/feature/FEATURES_THAT_WORK.md) |
| Test results | [08_tracking/test/test_result.md](08_tracking/test/test_result.md) |
| Bug reports | [08_tracking/bug/bug_report.md](08_tracking/bug/bug_report.md) |
| Build status | [08_tracking/build/recent_build.md](08_tracking/build/recent_build.md) |
| Project metrics | [10_metrics/README.md](10_metrics/README.md) |

---

## Quick Navigation

| # | Category | Purpose |
|---|----------|---------|
| 01 | **01_research/** | Research (local impl analysis, domain/external tech) |
| 02 | **02_requirements/** | Requirements (feature, nfr, ui) |
| 03 | **03_plan/** | Plans (arch, design, sys_test, agent_tasks) |
| 04 | **04_architecture/** | Architecture (ADRs, rules, formats, glossary) |
| 05 | **05_design/** | Design documents |
| 06 | **06_spec/** | SSpec-generated specs (mirrors src/) |
| 07 | **07_guide/** | User guides, tutorials |
| 08 | **08_tracking/** | Bug, test, todo, task, build tracking |
| 09 | **09_report/** | Implementation reports |
| 10 | **10_metrics/** | Dashboards, coverage |
| - | **archive/** | Historical/deprecated docs |
| - | **api/** | API docs |

---

## Document Relationship Model

```
01_RESEARCH -> 03_PLAN -> 02_REQUIREMENTS -> 06_SPEC -> BDD TESTS -> 08_TRACKING
                                  |
                                  +-> 02_REQUIREMENTS/nfr/
01_RESEARCH -> 05_DESIGN -> 04_ARCHITECTURE/adr/
07_GUIDE <- OPERATIONS
```

---

## Auto-Generated Docs (don't edit manually)

| File | Frequency |
|------|-----------|
| `06_spec/generated/feature.md` | Every test run |
| `06_spec/generated/pending_feature.md` | Every test run |
| `08_tracking/test/test_result.md` | Every test run |
| `08_tracking/build/recent_build.md` | Every build |
| `08_tracking/bug/bug_report.md` | `bin/simple bug-gen` |

---

## Pipeline

1. `/research_claude` -> 2. `/research_codex` -> 3. `/design_gemini` -> 4. `/design_codex` -> 5. `/design_claude` -> 6. `/impl` -> 7. `/verify` -> 8. `/refactor`

---

**Last Updated:** 2026-03-28
