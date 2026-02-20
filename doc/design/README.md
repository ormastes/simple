# Design Documentation

Technical design documents explaining how features work internally.

Design answers: **How is it built?**

---

## Document Types

| Type | Description |
|------|-------------|
| **Feature design** | Internal structure of a specific feature |
| **System design** | Cross-cutting architectural concerns |
| **Implementation plan** | Step-by-step build sequence |
| **Trade-off analysis** | Comparison of alternatives before a decision |

---

## Relationship in the Doc Model

```
RESEARCH (doc/research/)  →  informs  →  DESIGN  ←  (this folder)
                                               ↓
REQUIREMENTS (doc/requirement/)  →  drives  →  DESIGN
                                               ↓
                                         ADR (doc/adr/)  ← major decisions extracted here
```

---

## Document Template

```markdown
# Design – [Feature Name]

**Date:** YYYY-MM-DD
**Status:** Draft | In Progress | Complete
**Requirements:** [doc/requirement/xxx.md](../requirement/xxx.md)
**Research:** [doc/research/xxx.md](../research/xxx.md)

## 1. Context

What problem is this design solving?
What are the constraints and goals?

## 2. Components

- **Component A:** Responsibility and interface
- **Component B:** Responsibility and interface

## 3. Data Model

Key data structures and their relationships.

## 4. Key Decisions

- Decision 1: [rationale]
- Decision 2: [rationale]

For major decisions → create an ADR in `doc/adr/`

## 5. Failure Handling

| Failure Scenario | Response |
|-----------------|----------|
| Dependency X unavailable | Return error Y |
| DB failure | Return 503 |

## 6. Implementation Notes

Technical constraints, performance considerations, known limitations.
```

---

## Naming Convention

Files named: `<feature_name>.md` or `<feature_name>_design.md`

For dated iterations: `<feature_name>_design_YYYY-MM-DD.md`

Examples:
- `di_system.md`
- `type_inference_design.md`
- `mcp_server_architecture.md`

---

## When to Create a Design Doc

Create a design doc when:
- The feature involves multiple components or modules
- The implementation choice is non-obvious
- Others need to understand *why* it was built this way
- A major change to an existing system

For decisions within design docs → extract significant ones to `doc/adr/`.
