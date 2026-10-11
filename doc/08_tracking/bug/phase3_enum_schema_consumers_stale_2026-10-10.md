# Phase 3 enum consumers use obsolete payload shapes

The isolated native Phase 3 compiler self-build parses a 1166-module closure.
Its terminal HIR ledger contains 1157 PASS and nine FAILED records, so no
compiler artifact is published. Evidence:
`build/native_probe/explicit-call-types/parallel-phase-status.json` and
`phase3-probe-roots.log` in the isolated compiler repair checkout.

The failures are stale consumers of declared enum payloads: optimizer
CallTerminator/Send consumers; Send consumers in common text codegen, LLVM,
C and VHDL; LLVM library Compose/Parallel consumers; and frontend suspension
analysis Break/Continue consumers. The diagnostic messages include exact
payload-arity failures and ensuing unresolved bound names.

The parent candidate repairs the six non-optimizer owners to match the current
declarations. Unsupported backend Send paths retain their existing rejection
behavior. The CUDA Astra lane owns optimizer fixes and their payload/edge
regression checks. No full Phase 3 or Phase 4 PASS is claimed from these source
edits. The final native self-build must qualify the combined candidate.

## Combined probe outcome

The third bounded probe incorporates the parent repairs and Astra's optimizer
candidate `be8ddcaafc6` (cherry-picked as `5a91ca090e2`). Its immutable source
snapshot is `46496a10ea6c7d5c3d5c09c88c8b87ae43e48e153a9db668d6bc24f86046fbae`.
The authoritative terminal ledger contains 1166 PASS rows and no failures;
all 20 HIR workers finish with zero failed or unfinished modules.

The overall probe expires at its 300-second bound (exit 124) without an
artifact, a monomorphization result, or native compiler execution evidence.
An owned worker survives its parent timeout and receives SIGTERM. Evidence:
`phase3-combined.log`, `parallel-phase-status.json`, and
`phase3-combined-cache/default/frontend/queue-781939-0`. The three-probe cap
is reached; do not restart this full probe in the same session. Phase 4 has
not started and no new candidate is admitted for release.
