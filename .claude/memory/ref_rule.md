---
name: Engineering Rules Reference
description: Mandatory architecture, language, testing, documentation, VCS rules and override process
type: reference
---

## Architecture Rules
- Layer N imports only from layer ≤ N (00.common → 99.loader)
- No circular dependencies
- External systems behind interfaces
- Domain logic must NOT depend on infrastructure

## Language Rules
- ALL code in `.spl`/`.shs` — no Python/Rust/Bash (except 3 bootstrap scripts)
- Generics: `<>` not `[]`, Pattern binding: `if val` not `if let`
- NO inheritance — use composition, traits, mixins
- `?` is operator only, NO try/catch/throw — use Option/Result

## Testing Rules
- NEVER skip/ignore failing tests without user approval
- Fix root cause, not symptoms
- Built-in matchers only (see spipe skill)
- Every `*_spec.spl` must have module-level docstring

## Doc Rules
- Specs include Requirements/Plan/Design/Research links
- ADR required for major architectural decisions (`doc/04_architecture/adr/`)

## Code Style
- No over-engineering, no unused code, no magic numbers, no global mutable state

## Doc Folder Map
| Folder | Purpose |
|--------|---------|
| `doc/01_research/<domain>/` | Research and options |
| `doc/02_requirements/<domain>/` | Functional requirements |
| `doc/03_plan/<domain>/` | Plans, scope, milestones |
| `doc/04_architecture/<domain>/` | Architecture overviews |
| `doc/04_architecture/adr/` | ADRs |
| `doc/04_architecture/rule/` | Full rules: `README.md` |
| `doc/05_design/<domain>/` | Design documents |
| `doc/07_guide/<domain>/` | Developer guides |

Domains: `language`, `compiler`, `lib`, `app`, `os`, `hardware`, `platform`, `runtime`, `ui`, `ml`, `infra`

## Override: Only via ADR in `doc/04_architecture/adr/`
