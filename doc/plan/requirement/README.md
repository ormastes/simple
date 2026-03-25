# Requirements Documentation

Functional requirement documents for the Simple language project.

Each document records:
1. **User Request** — The original request as stated (verbatim or closely paraphrased)
2. **Interpretation** — Engineering team's understanding of what is needed
3. **System Requirements** — Formal REQ-NNN statements (what the system *shall* do)

Requirements answer: **What must the system do?**
They do NOT describe UI steps, API routes, or implementation details.

---

## Folder Relationship

```
PLAN
  ↓
REQUIREMENTS  ←  (this folder)
  ↓
FEATURE (BDD spec tests)
  ↓
TESTS

Parallel:
REQUIREMENTS → NFR       (doc/nfr/)
REQUIREMENTS → DESIGN    (doc/design/ or doc/architecture/)
RESEARCH     → DECISIONS → DESIGN
```

---

## Document Template

```markdown
# Functional Requirements – [Feature Name]

## User Request

> Original user request, verbatim or closely paraphrased.
> Include date and context if known.

## Interpretation

The requirement is understood as:
- Capability A: ...
- Constraint B: ...
- Edge case C: ...

Any ambiguities resolved:
- Ambiguity X resolved as: ...

## System Requirements

REQ-001:
The system shall ...

REQ-002:
The system shall ...

REQ-003:
The system shall NOT ...

## Out of Scope

- Item that was explicitly excluded
- Item deferred to future release

## Status

- [ ] Draft
- [ ] Reviewed
- [ ] Approved

## Cross-References

- **Plan:** [doc/plan/xxx.md](../plan/xxx.md)
- **Design:** [doc/design/xxx.md](../design/xxx.md)
- **Research:** [doc/research/xxx.md](../research/xxx.md)
- **Feature spec:** [test/xxx_spec.spl](../../test/xxx_spec.spl)
- **NFR:** [doc/nfr/xxx.md](../nfr/xxx.md)
```

---

## Naming Convention

Files named: `<feature-area>.md`

Examples:
- `authentication.md`
- `type_inference.md`
- `mcp_server.md`
- `di_system.md`
