# HIR worker deadline retirement records no reason (status=BLOCKED exit=-1)

Status: verification-pending
Date: 2026-11-20
Area: src/app/cli/worker_hir_owner_v1.spl (tick), native_build_main.spl HIR pool

## Symptom
Phase-2 stage2-compiler-tests row `compiler_cli_build` (also `test_runner_build`),
ubuntu-p2, release/1.0.0: all three HIR shard owners reaped as
`status=BLOCKED exit=-1 claimed=0 sealed=0 finished=false`, no `reason:` line.

## Evidence / root cause
- `summary.env`: `native_internal_timeout_seconds=1800`; row `elapsed_seconds=1832`.
- Ledger `full-cli/hir/queue-246623-0/BLOCKED` = `HIR worker retirement began: `
  (empty suffix), mtime 02:11, same second as the end of the log -> written at
  the first reap, not at spawn.
- Each worker's stdout segment (~8500 lines) is cut mid-line at the 1 MiB
  `stdout_limit_bytes` cap, still in `phase2:surface` (~seq 708 of 7005 files):
  workers were alive and in the whole-closure frontend prologue.
- `tick()` set `cancelled` on `now >= deadline_ms` without a reason; `code`
  stays -1 (init value, so the `-2` path never fires). The pool then wrote
  `retirement began: <empty>` and `hir_shard_reap_state_v1` reported BLOCKED
  (ledger already blocked) instead of TIMEOUT.

So: (1) not an RSS-guard kill — the 1800 s per-worker deadline expired while
workers were still re-parsing the closure (prologue too slow for the budget);
(2) observability defect: the deadline transition named nothing.

## Fix
`worker_hir_cancel_reason_v1` fills an empty reason on deadline expiry
("deadline expired after N s") or pool cancellation; owner records its launch
budget. Spec: `test/01_unit/app/cli/worker_hir_cancel_reason_v1_spec.spl`.

## Open
Prologue speed / budget: each worker re-parses ~7005 files (~150 s load +
surface) and does not finish the prologue in 1800 s; raise
`BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT` for these rows or share the
coordinator's parsed closure with workers. Reap state should also say TIMEOUT
when the owner retired on its own deadline.
