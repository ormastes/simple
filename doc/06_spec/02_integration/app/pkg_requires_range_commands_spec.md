# Product Package Range Commands

- Executable: `test/02_integration/app/pkg_requires_range_commands_spec.spl`
- Requirements: `KPM-REQ-009`, `KPM-REQ-011`, `KPM-REQ-012`, `KPM-REQ-014`
- Evidence class: executable SPipe definition; no execution result is embedded.

## Scenarios

- executes lock generate, lock check, and update dry-run through the root CLI
- publishes update output atomically through the root CLI and remains checkable
- keeps deterministic provider selection under declaration-order mutation
- fails unsatisfied ranges without mutating an existing lock
- preserves legacy lock and update behavior without interface declarations
- fails closed for malformed interface declarations without replacing the lock
- binds policy changes and rejects unknown policy without replacing the lock

## Selected Policy

The lock binds ABI v1 and the canonical `simple.sdn` manifest location.

## Freshness

The requirement IDs and scenario titles mirror the executable source. No
runtime PASS is claimed.
