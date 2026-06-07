# UI Test API Handler Test Specification

**Source:** `test/01_unit/app/ui.test_api/handler_test.spl`

## Summary

Handler-level coverage for the shared `/api/test/*` surface. The spec exercises
Protocol v1 ready/state/element/action routes and the Protocol v2 Draw IR
extension without opening sockets.

## Current Coverage

- 77 active scenarios, 0 skipped, 0 pending.
- Protocol v1 routes continue to return `protocol_version:1`.
- `/api/test/draw-ir*` requires `capability=draw_ir`.
- Draw IR success responses return Protocol v2 JSON/SDN payloads.
- Draw IR layout responses expose geometry, hit rect, clip/content/border rects,
  and computed style.
- Draw IR diff responses report stable-id geometry deltas and baseline-to-current
  per-node reports when `baseline=` is provided.

## Verification

```bash
bin/simple test test/01_unit/app/ui.test_api/handler_test.spl --mode=interpreter --clean
```
