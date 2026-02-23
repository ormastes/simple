# Engineering Rules

Mandatory engineering, architectural, testing, and operational rules governing the Simple language project.

Rules answer: **How must engineers work?**

These rules apply to all contributors. Overrides require an ADR (see `doc/adr/`).

---

## 1. Architectural Rules

### 1.1 Dependency Direction
- Dependencies point inward toward core logic
- Domain/business logic must NOT depend on infrastructure
- No circular dependencies between compiler layers
- Layer N may only import from layer ≤ N (numbered layer convention: `00.common`, `10.frontend`, etc.)

### 1.2 Layer Responsibilities

| Layer | Responsibility |
|-------|----------------|
| `00.common` | Error types, config, effects, shared types |
| `10.frontend` | Lexer, parser, AST |
| `15–35` | HIR, traits, types, semantics |
| `40–60` | Mono, MIR, optimization |
| `70` | Backends (C, LLVM, CUDA, Native) |
| `80–99` | Driver, tools, loader |

### 1.3 External Integration
- All external systems wrapped behind interfaces
- No third-party library calls inside domain/compiler core

---

## 2. Language Rules

### 2.1 Code Language
- **ALL source code in `.spl` or `.ssh`** — No Python, Rust, or Bash except 3 bootstrap scripts in `scripts/`
- **Generics:** `<>` not `[]` — `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **NO inheritance** — use composition, traits, or mixins
- **`?` is operator only** — never in names

### 2.2 Error Handling
- **NO try/catch/throw** — use Option pattern (`var error = nil`)
- Fail fast on programmer errors
- No silent error swallowing

### 2.3 Code Style
- No global mutable state
- No magic numbers — use named constants
- NEVER over-engineer — only make requested changes
- NEVER add unused code — delete completely

---

## 3. Testing Policy

### 3.1 Test Levels

| Level | Required | Purpose |
|-------|----------|---------|
| Unit | Yes | Business logic validation |
| Integration | Yes | Module boundary testing |
| BDD (SSpec) | Yes | User behavior scenarios |
| System | Yes | Full pipeline tests |

### 3.2 Rules
- **NEVER skip/ignore failing tests** without user approval
- **NEVER use `#[ignore]`** without user approval
- Always fix root cause — not the symptom
- Built-in matchers only: `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`

### 3.3 Coverage Policy
- All new features must have BDD scenarios
- Every spec file must have a module-level docstring

---

## 4. Documentation Policy

### 4.1 Spec File Requirements
Every `*_spec.spl` file must have:
- Module-level `"""..."""` docstring with Feature IDs, Category, Status
- Recommended: `**Requirements:**`, `**Plan:**`, `**Design:**`, `**Research:**` links

### 4.2 ADR Required When
- Introducing a new major dependency
- Changing persistence or storage technology
- Modifying the concurrency model
- Changing the security model
- Any decision with significant long-term impact

### 4.3 Doc Folder Structure

| Folder | Purpose |
|--------|---------|
| `doc/plan/` | Project plans (why, scope, milestones, risks) |
| `doc/requirement/` | Functional requirements (user request + interpretation) |
| `doc/nfr/` | Non-functional requirements / SLOs |
| `doc/design/` | Design documents |
| `doc/architecture/` | Architecture overviews |
| `doc/adr/` | Architecture Decision Records |
| `doc/research/` | Research and option analysis |
| `doc/guide/` | Developer guides, runbooks |
| `doc/rule/` | Engineering rules (this folder) |

---

## 5. Version Control Policy

- **NEVER use git** — use `jj` (Jujutsu)
- **NEVER create branches** — work directly on `main`
- Push: `jj bookmark set main -r @ && jj git push --bookmark main`
- Commit messages follow conventional format

---

## 6. Security Rules

- No secrets in repository
- Secrets injected via environment variables
- All tokens must expire
- Dependencies reviewed regularly
- Static security scan required before release

---

## 7. Enforcement

| Mechanism | What it catches |
|-----------|----------------|
| CI gates | Build failures, test failures |
| Linter (`bin/simple build lint`) | Code style violations |
| Code review | Architecture violations |
| `sspec-docgen` warnings | Missing doc links |
| Release checklist | Pre-release quality gates |

Rules may only be overridden via ADR in `doc/adr/`.
