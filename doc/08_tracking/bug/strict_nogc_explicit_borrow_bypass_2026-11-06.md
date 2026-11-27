# Strict no-GC explicit borrow-check bypass

- Status: open; source repair pending verification.
- Owner: release100 memory hardening lane (Codex).
- Requirements: recovery plan §3.7, AC-OWN-01, AC-CYCLE-04, AC-GATE-02.
- Baseline: e2ce7042552, release/1.0.0.

## Reproduction and boundary

`src/compiler/80.driver/driver_pipeline_passes.spl:21` returns true immediately
when `no_borrow_check` is selected, before inspecting MIR. The existing real-driver
spec `aot_borrow_gate_fail_closed_spec.spl` constructs Move(l1,l0) followed by
Copy(l2,l0), then explicitly expects success with this option. This is a
source-confirmed fail-open, not a new executable reproduction: no admitted
Stage 4 producer was available for this lane at audit time. The pure-Simple
owner makes the bypass decision; runtime/seed changes are not required.

The AOT path evicts HIR before calling the checker. Looking for strict modules
only in `ctx.hir_modules` would miss the ordinary native path. Preserve a compact
monotone policy fact from successful typed ownership admission until the context
ends. Failed admission remains fatal and cannot clear prior strict policy.

## Acceptance and limits

Reject the explicit bypass when any admitted module is strict, including a strict
dependency of a legacy entry and after HIR eviction. Preserve legacy diagnostic
bypass, fresh context defaults, failed-admission transactionality, and prior
error reporting. Run the existing real AOT seam regression plus the typed
admission spec using the admitted pure-Simple producer, with its negative
controls and exact source/runtime receipts. No runtime PASS is claimed here.

This repairs one option bypass; it does not establish interpreter CFG checking,
all-route deterministic cleanup, or any full recovery-plan acceptance row.
Token/provider telemetry: unavailable; no usage ratio inferred.
