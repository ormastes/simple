# Simple Language Documentation

Welcome to the Simple Language documentation. This directory is the single entry point for all project documentation.

---

## Start Here

| Resource | Description |
|----------|-------------|
| [guide/README.md](guide/README.md) | **The Simple Language Manual** -- getting started, tutorials, language reference |
| [spec/](spec/) | Formal language and tooling specifications |
| [architecture/](architecture/) | System design, compiler pipeline, module structure |
| [FILE.md](FILE.md) | Full documentation hub and relationship model |

---

## Directory Map

### Core

| Directory | Contents |
|-----------|----------|
| [guide/](guide/) | The Simple Language Manual (getting started, language, backends, FFI, testing, tooling) |
| [spec/](spec/) | Formal specs: [language/](spec/language/), grammar, parser, GPU/SIMD, testing, tooling |
| [architecture/](architecture/) | High-level architecture, module graphs, memory model, glossary |
| [design/](design/) | Internal design documents and proposals |

### Development

| Directory | Contents |
|-----------|----------|
| [plan/](plan/) | Implementation plans, roadmaps, refactoring strategies |
| [research/](research/) | Technical research, comparative analysis, feasibility studies |
| [feature/](feature/) | Feature tracking, status, and database |
| [requirement/](requirement/) | Requirements documents |
| [adr/](adr/) | Architecture Decision Records |

### Quality and Operations

| Directory | Contents |
|-----------|----------|
| [test/](test/) | Test results, coverage reports, test databases |
| [bug/](bug/) | Bug tracking and reports |
| [report/](report/) | Recent activity reports (older reports archived) |
| [build/](build/) | Build status and logs |
| [release/](release/) | Release notes and production readiness |

### Reference

| Directory | Contents |
|-----------|----------|
| [api/](api/) | API documentation |
| [examples/](examples/) | Code examples |
| [contributing/](contributing/) | Contributor guidelines |
| [format/](format/) | File format documentation (SDN, etc.) |
| [nfr/](nfr/) | Non-functional requirements |
| [rule/](rule/) | Engineering rules and conventions |

### Archived

| Directory | Contents |
|-----------|----------|
| [archive/](archive/) | Inactive docs: session/, dashboard/, task/, todo/, feature/usage/, feature/category/, old reports, and other historical material |

---

## Quick Commands

```bash
bin/simple doc-coverage             # Terminal coverage report
bin/simple doc-coverage --missing   # Show undocumented items
bin/simple build --warn-docs        # Check doc coverage during build
bin/simple stats                    # Show doc coverage in stats
```

---

## Auto-Generated Files

These files are updated automatically and should not be edited by hand:

| File | Updated by |
|------|------------|
| [feature/feature.md](feature/feature.md) | Every test run |
| [feature/pending_feature.md](feature/pending_feature.md) | Every test run |
| [test/test_result.md](test/test_result.md) | Every test run |
| [build/](build/) | Every build |
