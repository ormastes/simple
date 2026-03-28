# Documentation Writing Skill

## Document Relationship Model

```
PLAN -> REQUIREMENTS -> FEATURE SPEC -> BDD TESTS -> TEST RESULTS
REQUIREMENTS -> NFR;  RESEARCH -> DESIGN -> ADR;  GUIDES <- OPERATIONS
```

## Document Types & Locations

| Type | Location | Answers |
|------|----------|---------|
| Plan | `doc/plan/` | What and when |
| Requirement | `doc/plan/requirement/` | What must system do |
| Feature Spec | `doc/feature/` | How user experiences it |
| NFR / SLO | `doc/plan/nfr/` | How well must it work |
| Research | `doc/research/` | What to choose and why |
| Design | `doc/design/` | How it is built |
| Architecture | `doc/architecture/` | System structure |
| ADR | `doc/architecture/adr/` | Why this decision |
| BDD Tests | `test/*_spec.spl` | Executable scenarios |
| Guide / Runbook | `doc/guide/` | How to use/operate |
| Rule | `doc/architecture/rule/` | Engineering standards |
| Report | `doc/report/` | Session/completion reports |

## Critical Rules

- NEVER write spec.md files -- write `*_spec.spl` instead (executable SSpec tests)
- Specifications live in `test/` as executable BDD tests
- Research goes in `doc/research/`, NOT mixed with specs
- Use SDN for config/data, not JSON/YAML

## Documentation Workflow (New Features)

1. **Plan** -> `doc/plan/<feature>.md`
2. **Requirements** -> `doc/plan/requirement/<feature>.md` (REQ-NNN)
3. **Feature spec** -> `doc/feature/<feature>.md`
4. **NFR** -> `doc/plan/nfr/<feature>.md`
5. **Research** -> `doc/research/<feature>.md` (if non-obvious)
6. **Design** -> `doc/design/<feature>.md`
7. **ADR** -> `doc/architecture/adr/ADR-NNN-title.md` (major decisions)
8. **BDD Tests** -> `test/*_spec.spl` (link Requirements + Design in docstring)
9. **Guide** -> `doc/guide/<feature>_guide.md` (if applicable)
10. **Report** -> `doc/report/<feature>_complete_YYYY-MM-DD.md`

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
- `bin/simple doc-gen` to generate API docs from SSpec

## See Also

- `/sspec` for BDD test writing
- `doc/FILE.md` for document relationship model
