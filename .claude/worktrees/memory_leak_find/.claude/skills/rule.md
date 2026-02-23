# Engineering Rules Skill

Reference for the project's mandatory engineering, architectural, testing, and operational rules.

**Full rules document:** `doc/rule/README.md`

---

## Quick Reference

### Architecture
- Layer N imports only from layer ≤ N (numbered layer system: `00.common` → `99.loader`)
- No circular dependencies
- External systems behind interfaces
- Domain logic must NOT depend on infrastructure

### Language
- ALL code in `.spl` / `.ssh` — no Python, Rust, Bash (except 3 bootstrap scripts)
- Generics: `<>` not `[]` — `Option<T>`, `List<Int>`
- Pattern binding: `if val` not `if let`
- NO inheritance (`class Child(Parent)` is unsupported) — use composition, traits, mixins
- `?` is operator only — never in names
- NO try/catch/throw — use Option pattern

### Testing
- NEVER skip/ignore failing tests without user approval
- NEVER use `#[ignore]` without user approval
- Fix root cause — not symptoms
- Built-in matchers only (see `/sspec` skill)
- Every `*_spec.spl` must have a module-level docstring

### Documentation
- Spec files: include `**Requirements:**`, `**Plan:**`, `**Design:**`, `**Research:**` links
- `sspec-docgen` warns on missing links
- ADR required for major architectural decisions (see `doc/adr/`)

### Version Control
- Use `jj` (Jujutsu) — NEVER git
- Work on `main` directly — no branches
- Push: `jj bookmark set main -r @ && jj git push --bookmark main`

### Code Style
- No over-engineering — only make requested changes
- No unused code — delete completely
- No magic numbers
- No global mutable state

---

## Doc Folder Map

| Folder | Purpose |
|--------|---------|
| `doc/plan/` | Plans: why, scope, milestones, risks |
| `doc/requirement/` | Functional requirements (user request + interpretation) |
| `doc/nfr/` | Non-functional requirements / SLOs |
| `doc/design/` | Design documents |
| `doc/architecture/` | Architecture overviews |
| `doc/adr/` | Architecture Decision Records |
| `doc/research/` | Research and option analysis |
| `doc/guide/` | Developer guides, runbooks |
| `doc/rule/` | Engineering rules |

---

## Override Process

Rules may only be overridden via a formal ADR in `doc/adr/`.

No ad-hoc exceptions without documented rationale.

---

## See Also

- `doc/rule/README.md` — Full rules document
- `doc/adr/README.md` — ADR format and when to write one
- `doc/requirement/README.md` — Requirement format
- `/sspec` skill — Test writing rules and docstring metadata
- `/architecture` skill — Compiler layer structure
- `/versioning` skill — Jujutsu workflow
