# Render 8K80 container acceptance hardening gaps

Status: **RESOLVED / IMPLEMENTATION HANDOFF ACCEPTED (WARN)**

The container/GPU research, design, checker hardening, and Vulkan observation
work are complete. Independent highest-capability review accepted the corrected
implementation handoff as WARN. No A4, A5, or A7 acceptance item may be
promoted from this source-only state; live admitted receipts remain TODO810 and
TODO811.

## Checker and provenance gaps

- A4 and A5 have distinct workload hashes under a shared campaign contract.
- A4 validates exact per-frame and 20-frame considered, culled, rendered, and
  skipped command counts.
- Immutable runs retain a sorted hash manifest covering compiler provenance,
  native-build logs/timing, container identity, and CUDA qualification evidence.

## Device and process-verdict gaps

- Strict DrawIR requires exact backend-owner submit/fence deltas and rejects
  no-op or incomplete-fence evidence; the default producer requires 62/62.
- The strict producer returns 0/2/1 for pass/blocked/failed on both output paths.
- The physical wrapper does not yet emit the correlated physical receipt
  schema. Full promotion remains TODO684/TODO685.

## Unblock condition

Implementation unblock conditions are satisfied and deliberate-red coverage
detects each former defect. Campaign completion still requires running the live
paths with a provenance-admitted Stage 4 compiler (TODO810/TODO811) and, for
full PASS, correlated physical evidence (TODO684/TODO685).
