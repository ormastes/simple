# System Test Plan - Draw IR Inspection Contract

**Feature:** `draw_io_sdn_draw_ir`
**Executable spec:** `test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl`
**Generated manual:** `doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md`
**Status:** Red-phase pre-implementation contract tests

## Scope

This plan covers Draw IR Phases 4-6 before implementation starts: producer
enrichment, the gated Protocol-v2 `/api/test/draw-ir*` endpoint family, and the
`expect_draw` helper vocabulary.

It intentionally excludes GUI/2D/web framework implementation and pixel
evidence, which are owned by the parallel framework lane. These tests only pin
the contract surface and guardrails.

## Traceability

| REQ | Description | Test File | Test Cases | Coverage |
|-----|-------------|-----------|------------|----------|
| REQ-DRAW-INSPECT-001 | Protocol-v2 endpoint surface | `test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl` | endpoint family, route handling, version header, capability gate | Pre-impl |
| REQ-DRAW-INSPECT-002 | Producer enrichment | same | WM hit/clip rects, z-index, web computed style and rects | Pre-impl |
| REQ-DRAW-INSPECT-003 | `expect_draw` helper | same | helper export, `std.spec` embedding, geometry/hit/css/parent/kind vocabulary | Pre-impl |
| REQ-DRAW-INSPECT-004 | v1 compatibility | same | Protocol-v2 docs, v1 elements endpoint stability, empty-source negative case | Pre-impl |

## Execution

Run syntax/load checks before implementation:

```bash
bin/simple check test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl
```

The spec is expected to fail if executed before Phases 4-6 land, because it
asserts concrete future source markers instead of using placeholder false
assertions.
