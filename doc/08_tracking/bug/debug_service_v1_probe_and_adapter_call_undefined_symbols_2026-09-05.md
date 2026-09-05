# Bug: probe executor and interpreter adapter call undefined central-debug-service symbols

- **Filed:** 2026-09-05
- **Status:** OPEN (recorded, not fixed)
- **Area:** `src/lib/common/debug/`, `src/app/cli_debug/`, `src/app/debug/`
- **Severity:** blocker for the affected modules — they cannot compile

## Summary

Three modules code against a `central_debug_service_v1_*` / `contracts_v1`
surface that does not exist. Nothing defines the symbols below anywhere in the
tree (`grep -rn "fn <symbol>" src/` returns no definition), so every file that
imports them fails semantic resolution. The READ path
(`evidence_inspect_v1.spl`) was repaired on 2026-09-05 (see
`debug_evidence_inspect_receipt_id_field_missing_2026-09-05.md`); these are the
remaining gaps, deliberately left recorded rather than speculatively
implemented, because the callers disagree about the intended contract (an
explicit clock argument, a probe value type, and a receipt trail that
`service_v1.spl` does not currently retain).

## Undefined symbols and what each caller expects

### 1. `central_debug_service_v1_apply_probe`
- `src/app/cli_debug/probe_executor_v1.spl:17` (import), `:107` (call)
- Expected: `(DebugSessionId, DebugProbeKindV1, ...) -> <probe outcome>`, i.e.
  the service itself applies a probe to a target and returns its result.
  `service_v1.spl` owns only session/authorization bookkeeping and never talks
  to a target, so this needs a target-facing collaborator, not a new function
  on the existing registry.

### 2. `DebugProbeKindV1`
- `src/app/cli_debug/probe_executor_v1.spl:12` (import), `:107`
  (`DebugProbeKindV1.Stop`)
- Expected: an enum in `std.common.debug.contracts_v1` with at least a `Stop`
  variant. `contracts_v1.spl` has no such type.

### 3. `DebugRootOperationV1.Probe`
- `src/app/cli_debug/probe_executor_v1.spl:99,104,111,116,128,134`
- `src/app/debug/interpreter_service_adapter_v1.spl:95,100,103`
- Expected: a `Probe` variant on `DebugRootOperationV1`. The enum
  (`src/lib/common/debug/contracts_v1.spl:22-27`) carries only `Inspect`,
  `Control`, `Domain`, `Observe`, `Evidence`. Adding `Probe` is not free: every
  policy decision in `central_debug_service_v1_authorize`
  (`service_v1.spl`) would have to decide whether a probe is gated like
  `Control`, and no requirement states which.

### 4. `central_debug_service_v1_authorize_at` / `central_debug_service_v1_record_at`
- `src/app/debug/interpreter_service_adapter_v1.spl:18` (import); calls at
  `:59, 68, 82, 95, 100, 103, 110, 121, 122, 129, 134, 135, 142, 147, 148, 156`
- Expected: the same argument list as `_authorize` / `_record` plus a trailing
  `now_ns: i64` clock argument, so receipt times come from the caller rather
  than from the service. `service_v1.spl` records no timestamp at all today, so
  this is a contract change (a `captured_at_ns` field on `DebugReceiptV1`), not
  a wrapper.

### 5. `central_debug_service_v1_receipts`
- `test/01_unit/lib/nogc_async_mut/debug/legacy_service_adapter_v1_spec.spl:5`
  (import); calls at `:75, 87, 97`
- Expected: `(DebugSessionId) -> [DebugReceiptV1]` — the receipt trail for one
  session. `service_v1.spl` constructs receipts and returns them to the caller
  but **never stores them**: `_DebugSessionRecordV1` has no `receipts` field.
  Implementing this means the service starts retaining receipts, which is a
  memory-lifetime decision (unbounded growth per session) that should be made
  deliberately.

## Consequence today

`src/app/cli_debug/probe_executor_v1.spl` and
`src/app/debug/interpreter_service_adapter_v1.spl` are non-compiling, and
`test/01_unit/lib/nogc_async_mut/debug/legacy_service_adapter_v1_spec.spl`
cannot resolve its imports. Neither source file was touched by the 2026-09-05
read-path repair.

## Not to be "fixed" by weakening

Do not delete the call sites or stub the symbols to return empty values — an
unbacked debug receipt that silently returns nothing is exactly the failure
mode `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`
records. Each item above needs a stated contract first.
