# Architecture Decision Records (ADR)

Formal records of significant architectural decisions made during development.

ADRs answer: **Why was this technical decision made?**

---

## When to Write an ADR

Write an ADR when:
- Introducing a major new dependency
- Changing persistence or storage technology
- Modifying the concurrency or execution model
- Changing the security model
- Choosing between significantly different implementation approaches
- Any decision that is hard to reverse or has broad impact

---

## Document Template

```markdown
# ADR-NNN: [Short Title]

**Date:** YYYY-MM-DD
**Status:** Proposed | Accepted | Deprecated | Superseded by ADR-NNN

## Context

What is the issue or situation that motivates this decision?
What forces are at play (technical, team, timeline, constraints)?

## Decision

What is the change we are proposing or have decided to make?
State it as a clear, affirmative statement.

## Rationale

Why was this option chosen over the alternatives?

## Alternatives Considered

| Option | Pros | Cons |
|--------|------|------|
| Option A | ... | ... |
| Option B | ... | ... |
| Chosen option | ... | ... |

## Consequences

**Positive:**
- What becomes easier as a result

**Negative / Trade-offs:**
- What becomes harder or what debt is incurred

**Risks:**
- Known risks and mitigations

## References

- [Research document](../research/xxx.md)
- [Related requirement](../requirement/xxx.md)
- [Design document](../design/xxx.md)
```

---

## Naming Convention

Files named: `ADR-NNN-short-title.md`

Examples:
- `ADR-001-c-backend-for-bootstrap.md`
- `ADR-002-jujutsu-version-control.md`
- `ADR-003-numbered-compiler-layers.md`

## Status Lifecycle

```
Proposed → Accepted → (optionally) Deprecated
                   → Superseded by ADR-NNN
```
