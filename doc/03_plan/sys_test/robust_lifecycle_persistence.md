# Robust Lifecycle Persistence System Test Plan

## Scope

Prove that the convention-aligned pure-Simple model accepts valid lifecycle
metadata and fails closed on invalid graph, dependency, transition, and recovery
inputs. This plan does not claim storage or power-cut execution evidence.

## Scenarios

1. Define an ordered lifecycle graph and validate it.
2. Accept owner-to-longer dependency order and reject the reverse direction.
3. Reject duplicate levels, unknown endpoints, self edges, and cycles.
4. Validate complete transition metadata and reject missing policy fields.
5. Validate complete recovery registration and reject invalid schema or missing bindings.

## Traceability

- REQ-004: scenarios 1 and 3.
- REQ-005: scenario 2.
- REQ-006: scenarios 4 and 5.
- REQ-012: all scenarios.
- NFR-005: scenarios 3 through 5.

## Command

```sh
bin/simple test test/03_system/feature/language/robust_lifecycle_persistence_spec.spl --mode=interpreter
```

