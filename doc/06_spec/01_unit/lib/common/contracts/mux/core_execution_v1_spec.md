# CoreMux execution contract value controls

STATUS: NOT_RUN. Fourteen authored SSpec cases; zero executed, zero runtime passes.
Manual companion authored from the current spec; native docgen has not run.

Source: `test/01_unit/lib/common/contracts/mux/core_execution_v1_spec.spl`.
Production owners: `std.common.contracts.mux.execution_v1`, `observation_v1`,
`request_validation_v1`; canonical full provider interface is `port_v1.CoreMuxV1`.
Trace: REQ-CMUX-001/002/003/006/007/008/011, limited to typed representation
and validation boundaries. This does not satisfy real backend system requirements.

## Cases and observable assertions

| # | Step | Assertions |
|---:|---|---|
| 1 | Validate the closed mandatory command set | validates all thirty command shapes without issuing any operation |
| 2 | Reject forged target representation before mutation | rejects foreign owner incarnation and object kind with correlated errors |
| 3 | Check exact request and cell bounds | bounds relative deadlines IDs and terminal coordinates without overflow |
| 4 | Validate launch data without shell interpolation | preserves exec arguments Unicode environment and explicit shell mode |
| 5 | Preserve bytes and explicit input intent | keeps binary literal input distinct from paste keys and shell submission |
| 6 | Check typed key encoding bounds | accepts valid Unicode scalars and rejects surrogate keys and invalid function keys |
| 7 | Validate truncated capture and continuation | requires coherent byte extents and continuation for bounded captures |
| 8 | Preserve uncertainty instead of manufacturing rollback | retains partial native effects while unknown and expired receipts cannot assert NotApplied |
| 9 | Validate completeness of untrusted capability data | checks full descriptor coverage without converting NotRun evidence into qualification |
| 10 | Refuse incomplete descriptors before provider invocation | returns structured Unsupported for absent or unavailable mandatory operations |
| 11 | Validate observation and release requests | checks query context disconnect correlation and bounded event polling |
| 12 | Keep the original disconnect request ID on every validation error | preserves disconnect correlation on nested handle and deadline failures |
| 13 | Reject a receipt from another request or lease | binds reconciliation receipts to original owner incarnation token and request |
| 14 | Validate owner advertised lease duration and bounded receipt retention | bounds lease lifetime renewal cadence and retained history without creating authority |

All cases invoke actual production pure validators/mapping functions. The first
case validates every closed command and its distinct mandatory operation identity.
No provider stub, shell, terminal, process, server, timer or capability registry is
created. Test handle/receipt/capability records are intentionally untrusted data.
A Native descriptor with NotRun evidence is not support evidence; the tests assert
that the validator preserves NotRun. An Unsupported negative is a representation
check, not a backend feature pass or successful closed-gate system test.

## Execution gate and pending evidence

Run once only after an admitted current Phase3 compiler/runtime and matching full
modern SSpec runner exist. Retain producer/source/runtime hashes, actual argv,
exit status, case counts including failures, stdout/stderr and result artifacts.
No invocation is qualified by this manual; current execution is NOT_RUN.

Existing D1 discovery cases remain unchanged and unexecuted in this checkpoint.
Real providers still need actual owner authentication/membership, request ledger,
server deadlines, stale-revision refusal, real child execution/PTY capture,
reconnect/cleanup and independent-client tests on both Smux and tmux. Full N2 is
24 real hours per backend at the selected topology, not a simulated loop.


## Correction cycle 2

Disconnect validation now retains the supplied request ID even when nested handle
or deadline checks fail. Three added cases cover that correlation, reconciliation
receipt binding to the original owner/incarnation/token/request, and bounded lease
terms. Unicode environment preservation now checks the exact returned UTF-8 byte
sequence, not replacement ASCII test literals.

The full connection advertises owner-monotonic lease lifetime, renewal cadence,
fixed receipt retention and capacity. Receipt-only access cannot renew a lease or
slide retention. After expiry/revocation, only authenticated original-ID receipt
status or identical retained disconnect replay is permitted; no fresh operation,
metadata, capture or event authority returns. Unknown/evicted history cannot claim
NotApplied. These are contract rules and representation assertions, not executed
lease/clock/transport behavior. Actual idle renewal, expiry, non-sliding retention,
revoked-token refusal and no-revival tests remain required with real providers.
