# Actual signed Host pre-start fixture assertions

Status: AUTHORED_NOT_RUN fixture checker. Real admitted/native fault execution is
NOT_COVERED. Requires the existing signed Host harness and disposable runtime.

1. Preserve the actual writer lease and reservation ID. Execute a newly signed
   constrained Linux synchronous request or Windows synchronous/cooperative
   request through its real Host owner. Supply a deliberately mismatching
   restrictive expected configuration without changing the signed request.
2. Pass the actual completed failure to `check_real_pre_start_refusal_v1`.
   Assert `start_status=not-attempted`, the same writer lease, recovery required,
   and the reservation still present with a non-Released state. Keep the entire
   returned turn and settle through existing actual ownership, never a test DTO.
3. For an actual pending Windows native create/cancel cleanup, pass the retained
   turn to `check_real_pre_start_pending_cleanup_v1`. Assert the genuine
   continuation remains and no completed observation appears; continue actual
   owner cleanup in the harness while retaining the same Host charge.
4. Run exact matching, idempotent-existing-create, recovered-created, unknown
   configuration and mutated-runtime variants on each admitted platform. Only
   the matching current fresh-create transaction may proceed to existing start.
   The current fixture helpers do not claim these native variants were run.
5. For the actual successful current constrained create/start, pass the complete
   caller-owned turn to `check_real_pre_start_success_v1` with the original writer
   lease, reservation ID and exact observed runtime identity. Assert create/start
   OK, no error/recovery, exact runtime and retained charge. The helper returns
   the original turn and fails immediately on a missing actual observation.

Original absent-constraint APIs must preserve their existing behavior. Codex stdin,
CoreMux interactive control, resume history/workspace authority and app task
selection require their own genuine composition and are outside this checker.
