# Draw IR Protocol Evidence System Test Plan

## Scope

Verify that the UI test API exposes concrete Draw IR Protocol-v2 layout and
diff responses at system-test level, with generated manual evidence that can be
reviewed without opening the source test.

## Requirements

| Requirement | Evidence |
|-------------|----------|
| REQ-DRAW-EVIDENCE-001 | `/api/test/draw-ir/layout` returns Protocol-v2 geometry, hit rectangle, computed style, and kind fields. |
| REQ-DRAW-EVIDENCE-002 | `/api/test/draw-ir/diff` returns deterministic baseline diff fields for current and empty baselines. |
| REQ-DRAW-EVIDENCE-003 | The generated manual includes a JSON protocol capture artifact. |

## Execution

```sh
SIMPLE_LIB=src bin/simple-interp test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl
SIMPLE_LIB=src bin/simple check test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl
```

## Evidence

The spec writes:

`build/test-artifacts/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence/draw_ir_protocol.json`
