# System Test Plan - SGTTI Shared Surface Contract

**Feature:** `ui_test_sgtti`
**Executable spec:** `test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl`
**Generated manual:** `doc/06_spec/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md`
**Status:** Red-phase pre-implementation contract tests

## Scope

This plan covers SGTTI Phases 3-5 before implementation starts: lifting TUI
state to the shared WinText surface, running one body against `tui` / `gui` /
`both`, providing a single-call headless GUI snapshot helper, and pairing
semantic SGTTI assertions with Engine2D/web pixel evidence.

It intentionally excludes GUI/2D/web framework implementation. The executable
spec reads plans and source files only, so it can coexist with the parallel
framework lane.

## Traceability

| REQ | Description | Test File | Test Cases | Coverage |
|-----|-------------|-----------|------------|----------|
| REQ-SGTTI-SHARED-001 | TUI state lifts onto WinText | `test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl` | plan marker, access bridge, SGTTI constructor | Pre-impl |
| REQ-SGTTI-SHARED-002 | One body targets tui/gui/both | same | target constants, parity result, std.spec guardrail | Pre-impl |
| REQ-SGTTI-SHARED-003 | Headless GUI snapshot provider | same | plan contract, UI-test helper, compositor headless marker | Pre-impl |
| REQ-SGTTI-SHARED-004 | Semantic + pixel evidence pairing | same | Engine2D readback, SGTTI semantic check, web semantic check | Pre-impl |
| REQ-SGTTI-SHARED-005 | Framework boundary | same | imports stay source-only, empty-source negative, synthetic marker | Pre-impl |

## Execution

Syntax/load gate:

```bash
bin/simple check test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl
```

The spec is expected to fail if executed before Phases 3-5 land. Failures should
point at missing concrete markers, not placeholder false assertions.
