# Documentation Writing Skill

## Document Relationship Model

```
PLAN -> REQUIREMENTS -> FEATURE SPEC -> BDD TESTS -> TEST RESULTS
REQUIREMENTS -> NFR;  RESEARCH -> DESIGN -> ADR;  GUIDES <- OPERATIONS
```

## Document Types & Locations

| Type | Location | Answers |
|------|----------|---------|
| Research | `doc/01_research/<domain>/` | What to choose and why |
| Requirement | `doc/02_requirements/<domain>/` | What must system do |
| NFR / SLO | `doc/02_requirements/nfr/` | How well must it work |
| Plan | `doc/03_plan/<domain>/` | What and when |
| Architecture | `doc/04_architecture/<domain>/` | System structure |
| ADR | `doc/04_architecture/adr/` | Why this decision |
| Design | `doc/05_design/<domain>/` | How it is built |
| Feature Spec | `doc/06_spec/` | How user experiences it |
| BDD Tests | `test/*_spec.spl` | Executable scenarios |
| Guide / Runbook | `doc/07_guide/<domain>/` | How to use/operate |
| Rule | `doc/04_architecture/rule/` | Engineering standards |
| Tracking | `doc/08_tracking/` | Bugs, tests, build status |
| Report | `doc/09_report/` | Session/completion reports |

### Feature Domains (same across all doc phases)

| Domain | Scope |
|--------|-------|
| `language/` | Types, traits, generics, async, syntax, memory model |
| `compiler/` | Parser, codegen, backend, MIR, optimizer, SIMD |
| `lib/` | Stdlib: I/O, net, crypto, data structures, database |
| `app/` | CLI, MCP, IDE, editor, dashboard, build tools |
| `os/` | Kernel, drivers, desktop, storage, nvfs |
| `hardware/` | RISC-V, FPGA, baremetal, QEMU, HAL, RTL |
| `platform/` | FFI, SFFI, WASM, mobile, JS, cross-platform |
| `runtime/` | Native runtime, memory management, GC |
| `ui/` | GUI, TUI, browser rendering, 2D/3D, theme |
| `ml/` | Tensor, CUDA, Torch, deep learning |
| `infra/` | i18n, security, testing infra, CI/CD |

## Critical Rules

- NEVER write spec.md files -- write `*_spec.spl` instead (executable SPipe tests)
- Specifications live in `test/` as executable BDD tests
- Research goes in `doc/01_research/`, NOT mixed with specs
- Use SDN for config/data, not JSON/YAML

## doc/06_spec Structure (Generated vs Manual)

`doc/06_spec/` uses a 4-level hierarchy: `{category}/{domain}/{subdomain}/{file}`.

| Content | Naming | Lifecycle |
|---------|--------|-----------|
| **Generated** specs | `*_spec.md` (has `_Generated from` header) | Overwritten by `bin/simple spec-gen` |
| **Manual** specs | Non-`_spec.md` names (README, INDEX, guides) | Hand-edited, survives regeneration |
| **Auto-meta** | `feature.md`, `pending_feature.md` | Regenerated every test run |

Categories mirror test/ structure:
- `unit/` -> `test/01_unit/`, `integration/` -> `test/02_integration/`, `system/` -> `test/03_system/`
- `feature/` for language feature specs (language/, usage/)

Path mapping: `test/01_unit/compiler/parser/x_spec.spl` -> `doc/06_spec/unit/compiler/parser/x_spec.md`

See `doc/06_spec/FILE.md` for full manifest.

## Documentation Workflow (New Features)

1. **Research** -> `doc/01_research/<domain>/<feature>.md` (if non-obvious)
2. **Requirements** -> `doc/02_requirements/<domain>/<feature>.md` (REQ-NNN)
3. **NFR** -> `doc/02_requirements/nfr/<feature>.md`
4. **Plan** -> `doc/03_plan/<domain>/<feature>.md`
5. **Architecture** -> `doc/04_architecture/<domain>/<feature>.md`
6. **Design** -> `doc/05_design/<domain>/<feature>.md`
7. **ADR** -> `doc/04_architecture/adr/ADR-NNN-title.md` (major decisions)
8. **Feature Spec** -> `doc/06_spec/{category}/{domain}/{subdomain}/<feature>_spec.md` (generated from test)
9. **BDD Tests** -> `test/*_spec.spl` (link Requirements + Design in docstring)
10. **Guide** -> `doc/07_guide/<domain>/<feature>_guide.md` (if applicable)
11. **Report** -> `doc/09_report/<feature>_complete_YYYY-MM-DD.md`

## Research Document Format

```markdown
# Title - Research & Implementation Plan
**Date:** YYYY-MM-DD  |  **Status:** Research Phase
## 1. Problem Analysis (current state + requirements)
## 2. Proposed Solution (architecture + code examples)
## 3. Integration with Existing Infrastructure
## 4. Implementation Roadmap (phased tasks)
## 5. Testing Strategy
## 6. References
```

## Design Document Format

```markdown
# Component Design
**Status:** Draft | Review | Approved
## Overview, Design Principles, Architecture
## API Design (Simple code), Error Handling
## Performance/Security Considerations
## Alternatives Considered, Open Questions
```

## Writing Standards

- Clear, concise, active voice, present tense
- Working code examples (minimal, complete, commented)
- Semantic heading hierarchy, relative links for cross-refs
- `bin/simple doc-gen` to generate API docs from SPipe

## See Also

- `/spipe` for BDD test writing
- `doc/FILE.md` for document relationship model
