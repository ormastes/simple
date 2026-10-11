# Phase 3 closed timeout classification and receipt validation

Canonical diagnostic ID: BUG-BOOTSTRAP-PHASE3-CLOSED-TIMEOUT-2026-10-11.
Bug database reconciliation is pending; no qualified bug DB tool was used in this
bootstrap orchestration lane. This report is the dated provisional bug record.

## Retained failure

`build/native_probe/phase3-original1220-80030-20261010/chunk06-final-cycle3/`
is pinned to request SHA-256
`ea6e128831d5b86263357d0dd0073344e632a1a0da7b887a972820958ef37bd5` and producer
`80030da7da3f15174dc26285389375b19c8f090c29eedb6bded089defaa28071`.
Its 160 rows are not 160 compiler executions: 125 dispatches produced 117 raw
terminal rows plus eight controller-classified unsafe rows; 35 were not launched.
The raw exit grouping is 63 exit-1, ten exit-0, 44 access violations (139), eight
timeouts (124), and 35 absent exits. Object validity remains an independent gate.

The eight timeout rows are modules 0373, 0539, 0649, 0715, 0760, 1038, 1082, 1092.
The controller asserted `unknown Job status` because it admitted only `complete`
and `rss-cap-exceeded`, even though canonical receipts explicitly reported
`status=timeout`, exit 124, `timeout_signal=job-terminate`, and `quiescent=1`.
That classification stopped independent work. The task budget was 120 seconds;
no automatic retry remains after cycle three.

Independent read-only authentication verified all eight receipts: Job containment
without breakaway, helper integrity and actual executable hash, enforced matching
1-GiB caps, positive samples/peaks, no duplicate fields, complete capture, no dropped
bytes or observer/reader/retention/diagnostic errors, matching actual retained-log
bytes/hashes, and actual diagnostic-summary hashes. Peaks were 947,652–969,044 KiB,
below the cap. Original runner, results, audit, logs, and caches were not rewritten.
These are **closed timeout failures safe for independent continuation**, not passes.

## Minimal host gate reproductions

The existing packet contains `timeout_gate_controls_sol.py`. It extracts only
`sha` and `receipt_safe` from the exact runner AST; it never imports launch code or
invokes a compiler. Synthetic receipts use independently pinned temporary fixture
bytes and exact negative mutations. They do not claim a real Job execution.

Original runner SHA-256:
`ac3bae3e5c7fae0987ae29156acf49855f7d396344824e63e6c00cf04a883c80`.
Original receipt gate AST SHA-256:
`c15732096803fbcae1c1e1654d822ba6cdcce6b071cfa1c9ea258c977a8d6cb9`.
The baseline has 23 of 28 controls passing and five failing:

- Rejects an authenticated closed timeout.
- Accepts duplicate `quiescent=0` followed by `quiescent=1` on a closed AV receipt.
- Accepts a nonempty live-observer error.
- Accepts disagreement between retained-log and stream SHA-256 metadata.
- Accepts a retained-byte count that disagrees with actual captured output.

The other controls cover missing closure/receipt, unsafe or changed helper bytes,
log/diagnostic drift, incomplete/dropped capture, exit mismatch, incorrect timeout
signal/code, missing RSS samples/peak, unenforced/mismatching cap, unknown status,
reader/retention/diagnostic errors, and unsafe containment. Complete AV and RSS-cap
failures remain closed failures eligible for independent continuation.

## Repair boundary

Repair only the new continuation runner before freezing its request. Reject
duplicate fields before building a dictionary. Keep all original closure, helper,
resource, exit, log and diagnostic hash checks; add stream byte/hash consistency
and observer error checks. Admit `timeout` only for exit 124 plus proven canonical
Job termination and closure. Record it as a failed timeout; never mark it green.
Missing or contradictory evidence still stops the continuation.

Preserve old producer/source/entry caches and failed attempt logs. Run independent
untouched entries with the separately qualified new producer; rerun an old failure
only after a bounded new-producer reproduction is authorized. No source workaround,
memory-safety relaxation, compiler restart, or cache deletion is part of this repair.
No temporary workaround tag or applied source-fix SHA is claimed.

The 44 AV rows all end at MIR `lower_to_mir` after successful HIR validation under
the old producer. This is a shared stage classification, not a proven shared cause.
Current-producer reproduction and fault evidence are required before changing MIR
or memory ownership code. No new AV/native compilation was launched in this review.

The new `chunk07a-run/run_batch.py` gate passed all 30 controls, with zero compiler
invocations. Two additional controls check truly absent closure and RSS fields;
the original 28-control baseline was preserved without rerunning it. Runner bytes
were identical before and after testing. Tested runner SHA-256:
`79d926636cc9ec68d21dc7a0e52c8d18e407a2fb4c09a6324057a7c98475b899`.
Tested receipt gate AST SHA-256:
`b2d6c260aa395701651d4d5be2a8aace119bd892c97121c8d8083ae652955ff6`.
The gate accepts closed timeout/AV/RSS failures for independent continuation while
every invalid control fails closed. It does not change the compiler result.

Current evidence: `timeout-authentication-sol-v2.json`,
`timeout-gate-controls-sol-before.json`, and `timeout-gate-controls-sol.json` in the
existing final-cycle packet. The continuation owner must bind the tested gate to
its final frozen request; execution admission remains root-owned. This document
does not admit a global Phase 3 pass, relabel the 35 unlaunched rows, or claim a
landed compiler source fix.
