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
- Built-in matchers only (see sspec skill)
- Every `*_spec.spl` must have module-level docstring

## Doc Rules
- Specs include Requirements/Plan/Design/Research links
- ADR required for major architectural decisions (`doc/architecture/adr/`)

## Code Style
- No over-engineering, no unused code, no magic numbers, no global mutable state

## Doc Folder Map
| Folder | Purpose |
|--------|---------|
| `doc/plan/` | Plans, scope, milestones |
| `doc/plan/requirement/` | Functional requirements |
| `doc/design/` | Design documents |
| `doc/architecture/` | Architecture overviews |
| `doc/architecture/adr/` | ADRs |
| `doc/research/` | Research and options |
| `doc/guide/` | Developer guides |
| `doc/architecture/rule/` | Full rules: `README.md` |

## Override: Only via ADR in `doc/architecture/adr/`
