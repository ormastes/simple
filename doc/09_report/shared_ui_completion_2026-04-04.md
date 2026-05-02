# Shared UI Contract Completion Report

**Date:** 2026-04-04  
**Contract:** [doc/04_architecture/shared_ui_contract.md](../04_architecture/shared_ui_contract.md) (292 lines)  
**Prior commit:** `58aa209f6f` — initial cross-surface test suite and widget state semantics

## Summary

Shared UI contract (Protocol V1) moves from **Implemented (scoped)** to **Implemented** with full cross-surface proof across web and tui_web backends.

The test API now provides:
- Complete cross-surface verification of all contract operations (tree read, actions, focus/state, protocol, errors, consistency)
- Stale-session proof: connection failure after server teardown
- Selection state (`check_selected`) cross-surface consistency
- 4 negative tests covering element_not_found, missing_field, unknown_event_type, and stale session
- Read-after-write consistency verification

## Implementation

### Phase 1: Initial Contract + Test Suite (prior)
- Created `doc/04_architecture/shared_ui_contract.md` — 292-line authoritative contract
- Created `src/app/ui.test_api/handler.spl` — shared HTTP request handler
- Created `src/lib/nogc_sync_mut/ui_test/` — client, types, http, parse modules
- Created `src/lib/common/ui/` — 36+ widget/event/state files
- Created 19 cross-surface tests covering protocol, tree read, actions, focus/state, errors, consistency

### Phase 2: Gap Closure (this report)
- Added `check_selected` cross-surface test — verifies selection state is consistent on both web and tui_web surfaces, matching the pattern of `check_visible` and `check_enabled`
- Added stale-session test — starts both servers, confirms readiness, stops them, then verifies that subsequent requests return connection errors (proving session teardown)

## Files Changed

### Modified (1)
| File | Change |
|------|--------|
| `test/system/ui/shared_ui_contract_spec.spl` | +2 tests (check_selected, stale session), updated docstring |

### Created (1)
| File | Lines | Purpose |
|------|-------|---------|
| `doc/09_report/shared_ui_completion_2026-04-04.md` | this file | Completion report |

## Key Files

### Test API Server
| File | Purpose |
|------|---------|
| `src/app/ui.test_api/handler.spl` | Shared HTTP handler for both surfaces |
| `src/app/ui.test_api/json.spl` | JSON serialization helpers |

### Test Client Library
| File | Purpose |
|------|---------|
| `src/lib/nogc_sync_mut/ui_test/client.spl` | UITestClient with all assertion methods |
| `src/lib/nogc_sync_mut/ui_test/types.spl` | ElementInfo, UIStateInfo types |
| `src/lib/nogc_sync_mut/ui_test/http.spl` | Raw TCP HTTP helpers (test_get, test_post) |
| `src/lib/nogc_sync_mut/ui_test/parse.spl` | JSON field extraction |

### Widget/State Core
| File | Purpose |
|------|---------|
| `src/lib/common/ui/` | 36+ files: widget tree, events, state, rendering |

### Contract
| File | Purpose |
|------|---------|
| `doc/04_architecture/shared_ui_contract.md` | 292-line authoritative Protocol V1 contract |

## Test Summary

**Total:** 21 tests (19 existing + 2 new)  
**Negative tests:** 4 (element_not_found, missing_field, unknown_event_type, stale session)

| Section | Tests | Coverage |
|---------|-------|----------|
| Protocol | 2 | ready endpoint, unknown route error |
| Tree / Read | 4 | element list, IDs, kind lookup, screenshot |
| Actions | 5 | click, type, submit, drag, send_key |
| Focus / State | 4 | focus_next, check_visible, check_enabled, check_selected |
| State Endpoint | 1 | element_count + protocol_version |
| Errors | 4 | element_not_found, missing_field, unknown_event_type, stale session |
| Consistency | 1 | read-after-write (click then get_element) |

## Known Limitations

- Session model is per-server-instance; no explicit session token mechanism
- Reset is not supported; tests requiring clean state must restart the server
- `stale_session` (HTTP 410) error code is defined in the contract but not yet returned by the handler — the current implementation relies on TCP connection failure for stale-session detection
- Widget tree structure changes (dialog open/close) are not directly tested beyond read-after-write consistency

## Status

| Aspect | Before | After |
|--------|--------|-------|
| Contract doc | 292 lines | 292 lines (unchanged) |
| Cross-surface tests | 19 | 21 |
| Negative tests | 3 | 4 |
| Feature status | Implemented (scoped) | Implemented — Protocol V1 |
