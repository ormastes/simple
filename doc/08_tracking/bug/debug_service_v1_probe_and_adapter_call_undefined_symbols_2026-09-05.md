# Bug: probe executor and interpreter adapter call undefined central-debug-service symbols

## RESOLVED 2026-09-06 (items 1-4); item 5 STILL OPEN

Both named modules now compile and are covered by running specs. Defined:

- `DebugRootOperationV1.Probe` (`contracts_v1.spl`) — no `match` in the tree is
  exhaustive over this enum (`grep -rn "case DebugRootOperationV1" src test` is
  empty), so the variant broke nothing. **Stated contract, previously unchosen:
  Probe is gated by `DebugPolicyV1.allow_control`** — applying or removing a
  probe modifies the debuggee, so a policy denying Control denies Probe.
- `DebugProbeKindV1` with a single `Stop` variant — the only kind any caller
  applies through the central service.
- `DebugProbeV1` (`probe_id`, session, kind, target, anchor, perturbation,
  expiry) and `central_debug_service_v1_apply_probe(...) -> Result<DebugProbeV1, text>`.
  The service still never contacts a target: `probe_executor_v1.spl` already
  sends `break` through its own transport *before* calling this, so the service's
  job is validate-and-mint — session open, target registered, then a session-bound
  `probe-<session>-<n>`. It fails closed on an unknown session or unregistered
  target; it does not claim the probe is live.
- `central_debug_service_v1_authorize_at` / `_record_at` — the real
  implementations, carrying the caller's `now_ns` onto a new
  `DebugReceiptV1.captured_at_ns` field. `_authorize`/`_record` keep their exact
  signatures and delegate with `-1`, meaning "caller supplied no clock" — never a
  synthesised timestamp.

Caller edits (each unreconcilable with any sane definition, stated per the rule):

- `interpreter_service_adapter_v1.spl:116` called
  `central_debug_service_v1_update_target_capability_at(..., now_ns)`, a symbol
  this record never listed. `DebugCapabilityV1` carries no timestamp field and is
  constructed positionally at ~8 sites, so an `_at` form would have accepted the
  clock and dropped it — the unbacked-wrapper failure mode this record forbids.
  Defined `central_debug_service_v1_update_target_capability(session_id, capability)`
  (replaces an already-registered target's capability; Err on unknown session or
  unregistered target) and dropped `_at`/`now_ns` at the call site.
- Both modules imported `debug_policy_development_v1` from `contracts_v1`, which
  does not provide it (`[use-warning]` at run time); the import moved to
  `service_v1`.

Specs: `test/01_unit/app/cli_debug/probe_executor_v1_spec.spl` (5/5) and the new
`test/01_unit/app/debug/interpreter_service_adapter_v1_spec.spl` (3/3).
Regression cover unchanged: `evidence_inspect_v1_spec` 5/5,
`debug_evidence_bundle_contract_v1_spec` 7/7,
`central_debug_service_v1_lifecycle_spec` 6/6.

### STILL OPEN

- **Item 5, `central_debug_service_v1_receipts`** — not implemented. The service
  still retains no receipts (`_DebugSessionRecordV1` has no `receipts` field), and
  the module its legacy spec imports,
  `src/lib/nogc_async_mut/debug/legacy_service_adapter_v1.spl`, does not exist. It
  was deliberately NOT created and the spec was NOT deleted. ~20 further specs
  across `test/` import `central_debug_service_v1_receipts` (and
  `_graph` / `_session`), so retention is a deliberate memory-lifetime decision for
  the lane that owns it, not a side effect of this fix.
- `src/app/debug_adapter_host_v1.spl:17,118` still imports and calls
  `central_debug_service_v1_update_target_capability_at`; it needs the same
  one-line call-site change (out of this lane's file scope).
- `InterpreterDebugServiceAdapterV1.set_semantic_breakpoint` and `.close()` are
  unrunnable under the seed interpreter: `rt_debug_add_breakpoint` and
  `rt_debug_remove_all_breakpoints` fail with "unknown extern function"
  (observed 2026-09-06). The adapter compiles and `launch` works; the new spec
  therefore closes the session through the service instead of through the
  adapter. This is a runtime-backing gap, not a spec-scoping choice.
- `DebugRootOperationV1.Profile` (referenced by
  `test/01_unit/lib/debug/remote/protocol/t32_debug_service_adapter_v1_spec.spl`)
  and `DebugProbeKindV1.Log/Watch/Trace` (referenced by specs calling a
  `service.apply_probe` OBJECT api that does not exist) were NOT added — no
  compiling caller needs them.

---

- **Filed:** 2026-09-05
- **Status:** RESOLVED 2026-09-06 for items 1-4; item 5 OPEN
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
