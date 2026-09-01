# Stage 4 bootstrap receipt planner unavailable

**Status:** open preflight defect; bootstrap transaction not started by the
planner failures. **Observed:** 2026-08-15.

The frozen Stage-4 worktree passed the required
`.stage4-frozen-inputs.sha256` hash and all 27,066 listed-file checks, but the
first guarded bootstrap invocation stopped before Stage 1 with exit 64:

```text
bootstrap-policy-error: reason-receipt-required; run 'simple build bootstrap --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path>'
```

No Simple source file or module was processed. The worktree has no
`bin/simple`. `bin/release/simple` resolves the retained full CLI at
`release/x86_64-unknown-linux-gnu/simple`; that binary reports
`Simple v1.0.0-beta` but exits by SIGSEGV (139) for both the compiled
`build bootstrap` planner and the source-run CLI planner. Its SHA-256 is
recorded in the Stage-4 owner receipt. The retained Stage-3 executable reports
`simple-bootstrap 1.0.0-beta` and rejects `build` as an unknown command.

The bootstrap guard's own exact regression
`scripts/check/check-bootstrap-reason-receipt-guard.shs` constructs and
validates the canonical non-cryptographic receipt string directly. For this
frozen recovery only, the owner may construct that same receipt with reason
`self-host-convergence-check`, run `--validate-bootstrap-receipt`, and retain
the exception in the transaction evidence. This does not claim that the
broken planner produced the receipt and does not resolve the planner crash.

The follow-up owner must reproduce the full-CLI SIGSEGV with an exact System
case and a smallest Integration case at the failing runtime/dispatcher owner.
