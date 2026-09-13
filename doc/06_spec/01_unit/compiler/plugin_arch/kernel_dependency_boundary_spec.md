# Kernel Dependency Contracts

- Executable: `test/01_unit/compiler/plugin_arch/kernel_dependency_boundary_spec.spl`
- Requirements: `KPM-REQ-001`, `KPM-REQ-007`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution result is embedded.

## Scenarios

- constructs the API surface contract without tool ownership
- provides shared-library policy from the kernel contract
- keeps call scanning in semantic ownership

## Freshness

The requirement IDs and scenario titles mirror the executable source. No
runtime PASS is claimed.
