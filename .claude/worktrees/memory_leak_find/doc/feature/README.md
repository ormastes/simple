# Feature Documentation

Feature Specification documents — the bridge between Requirements and BDD tests.

Feature answers: **How does the user experience the requirement?**

---

## Two Types of Content

| Content | Description |
|---------|-------------|
| **Auto-generated** | `feature.md`, `pending_feature.md` — updated by test runner every run |
| **Feature Specifications** | BDD narrative docs linking REQ-NNN to test scenarios |

**Do not edit `feature.md` or `pending_feature.md` manually** — they are overwritten on every test run.

---

## Relationship in the Doc Model

```
PLAN (doc/plan/)
  ↓
REQUIREMENTS (doc/requirement/)
  ↓
FEATURE SPECIFICATION  ←  (this folder)
  ↓
BDD TESTS (*_spec.spl in test/)
  ↓
TEST RESULTS (doc/test/test_result.md)
```

Requirements → generates → Feature Specification(s)
Feature Specification → verified by → BDD Tests

---

## Feature Specification Template

```markdown
# Feature Specification – [Feature Name]

**Requirements:** [doc/requirement/xxx.md](../requirement/xxx.md)
**Plan:** [doc/plan/xxx.md](../plan/xxx.md)
**Design:** [doc/design/xxx.md](../design/xxx.md)
**Status:** Draft | In Progress | Implemented | Complete

## Feature Description

One sentence: what capability does this provide to the user?

## Scenarios

### Scenario: [Happy Path Name]

**Given** [precondition — system or user state]
**When** [user action or system event]
**Then** [expected observable outcome]

### Scenario: [Edge Case Name]

**Given** [precondition]
**When** [action]
**Then** [expected outcome]

### Scenario: [Error Case Name]

**Given** [invalid state or input]
**When** [action]
**Then** [expected error behavior]

## Acceptance Criteria

- [ ] Criterion 1 (measurable)
- [ ] Criterion 2 (measurable)
- [ ] Criterion 3 (measurable)

## Out of Scope

- What this feature does NOT cover
- Deferred capabilities

## Test Coverage

| Scenario | Spec file | Status |
|----------|-----------|--------|
| Happy path | test/xxx_spec.spl | ✅ Passing |
| Edge case | test/xxx_spec.spl | ✅ Passing |
```

---

## Naming Convention

Files named: `<feature_name>.md`

Examples:
- `password_reset.md`
- `type_inference.md`
- `mcp_server_protocol.md`
- `di_system.md`

---

## Cross-References

Feature specs should link to:
- `doc/requirement/` — the REQ-NNN statements driving this feature
- `doc/plan/` — the plan for implementation
- `doc/design/` — the technical design
- `test/*_spec.spl` — the BDD test files that verify it
