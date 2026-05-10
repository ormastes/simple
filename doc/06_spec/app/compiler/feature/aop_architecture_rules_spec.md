# AOP Architecture Rules Specification

**Feature ID:** #AOP-ARCH-001 to #AOP-ARCH-010 | **Category:** Language | **Status:** Implemented

_Source: `test/feature/usage/aop_architecture_rules_spec.spl`_

---

## Syntax

```simple
# Forbid pattern with error message
forbid pc{ import(from_pattern, to_pattern) } "Error message"
forbid pc{ depend(from_pattern, to_pattern) } "Error message"

# Allow pattern (exceptions)
allow pc{ depend(within(api.**), within(core.**)) } "Allowed exception"
```

## Architecture Selectors

| Selector | Description |
|----------|-------------|
| import(from, to) | Match import statements |
| depend(from, to) | Match module dependencies |
| use(pattern) | Match type/function usage |
| export(pattern) | Match exported symbols |
| config(string) | Match configuration values |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 27 |

## Test Structure

### Architecture Forbid Rules

#### import rules

- ✅ forbids importing test internals in production
- ✅ forbids importing implementation details
#### dependency rules

- ✅ forbids domain depending on infrastructure
- ✅ forbids circular dependencies
#### usage rules

- ✅ forbids using Container in domain
- ✅ forbids using deprecated types
#### config rules

- ✅ forbids test config in release
### Architecture Allow Rules

#### selective allows

- ✅ allows api to depend on core
- ✅ allows test code to use internal modules
#### priority-based overrides

- ✅ allow with higher priority overrides forbid
### Layered Architecture Constraints

#### three-tier architecture

- ✅ defines presentation layer constraints
- ✅ defines application layer constraints
- ✅ defines domain layer constraints
#### hexagonal architecture

- ✅ enforces port-adapter boundaries
### Module Boundary Rules

#### internal modules

- ✅ forbids importing internal submodules
- ✅ requires using public facade
#### export restrictions

- ✅ forbids exporting internal types
### Security Architecture Rules

#### credential access

- ✅ restricts credential usage
- ✅ forbids storing secrets in plain text
#### network boundaries

- ✅ restricts direct network access
### Test Isolation Rules

#### test-only code

- ✅ forbids mock in production
- ✅ forbids test utilities in production
#### test profile restrictions

- ✅ forbids test profile in release
### Architecture Rule Diagnostics

#### violation messages

- ✅ provides actionable error message
- ✅ identifies violation location
### Architecture Rule Composition

#### complex patterns

- ✅ combines multiple conditions
- ✅ uses negation for exceptions

