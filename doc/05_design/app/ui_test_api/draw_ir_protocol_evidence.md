# Draw IR Protocol Evidence Design

## Overview

`draw_ir_protocol_evidence_spec.spl` is a system-level evidence wrapper around
the real `app.ui.test_api.handler.handle_test_request` entrypoint. It uses an
in-process `UIState` fixture and records layout/diff responses as protocol
evidence.

## Data Flow

1. Build a `UIState` with a stable root widget.
2. Call `/api/test/draw-ir/layout?id=root&capability=draw_ir`.
3. Call `/api/test/draw-ir/diff?baseline=current&capability=draw_ir`.
4. Call `/api/test/draw-ir/diff?baseline=empty&capability=draw_ir`.
5. Write status, content type, and JSON bodies to
   `build/test-artifacts/.../draw_ir_protocol.json`.

## Boundaries

The spec does not start a web server or browser. It verifies the same protocol
handler that production UI test clients call, while keeping the evidence
deterministic and host-independent.
