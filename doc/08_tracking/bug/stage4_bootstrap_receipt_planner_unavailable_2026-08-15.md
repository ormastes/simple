# Stage 4 bootstrap receipt planner unavailable
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** BLOCKED (kept OPEN), re-confirmed 2026-11-11 (lane boot23); grant verbatim below. **Observed:** 2026-08-15.

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


## Addendum 2026-11-11 — P3 boot15 lane triage (worktree simple-p3-boot15-20261111, base f7640d20a458)

**Verdict: BLOCKED — kept OPEN.** The frozen-worktree full-CLI SIGSEGV (exit 139 on
both the compiled `build bootstrap` planner and the source-run CLI planner) needs a
Stage-3/4 chain to reproduce; none can run on the Windows lane host. The current
Stage-4 frontier is `stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01.md`
(OPEN), which this record's follow-up owner should read first — the full CLI it
targeted can no longer even link, so this record's planner crash is behind that wall.

Guard-side spot-check executed by this lane: `sh scripts/check/check-bootstrap-reason-receipt-guard.shs`
-> `FAIL: missing receipt did not return the canonical diagnostic`. Diagnosed as a
LANE-WORKTREE ARTIFACT, not the guard: in this fresh-seed worktree the bootstrap
script exits 70 in preflight on 562 unsmudged Git LFS pointer files (PNG/vendor
binaries) before the receipt guard is ever consulted. On an LFS-smudged host this
check remains the guard's exact regression; re-run it there as part of the grant.

**Grant (non-Windows host, x86_64-unknown-linux-gnu, LFS-smudged worktree):**
first `sh scripts/check/check-bootstrap-reason-receipt-guard.shs` (must PASS — it is
the guard's exact regression), then reproduce the planner crash:
`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` through Stage 3,
then `bootstrap/stage3/x86_64-unknown-linux-gnu/simple build bootstrap --bootstrap-reason=self-host-convergence-check --bootstrap-receipt=<owner-constructed-receipt>`
to obtain the failing System/Integration case at the runtime/dispatcher owner, exactly
as this record's follow-up sentences require. The owner-constructed receipt exception
for this frozen recovery remains as recorded above.

## Addendum 2026-11-11 (lane boot23) — BLOCKED re-confirmed; boot15 disposition stands

Re-verification at this lane's base (`41935a5f61860`), one source check:
the current Stage-4 frontier this record's follow-up owner must read first,
`stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01.md`,
still carries `Status: **OPEN**` at this tip — the full-CLI target still
cannot link, so this record's planner SIGSEGV (exit 139) remains behind that
wall and unreachable from this Windows lane host.

Disposition unchanged: **BLOCKED** (kept OPEN). boot15's guard-side spot-check
artifact (fresh-worktree LFS preflight exit 70 before the receipt guard runs)
also stands — re-run the guard on an LFS-smudged host.

Verbatim grant (non-Windows host, x86_64-unknown-linux-gnu, LFS-smudged
worktree):
first `sh scripts/check/check-bootstrap-reason-receipt-guard.shs` (must PASS —
it is the guard's exact regression), then reproduce the planner crash:
`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` through Stage 3,
then `bootstrap/stage3/x86_64-unknown-linux-gnu/simple build bootstrap --bootstrap-reason=self-host-convergence-check --bootstrap-receipt=<owner-constructed-receipt>`
to obtain the failing System/Integration case at the runtime/dispatcher owner,
exactly as this record's follow-up sentences require. The owner-constructed
receipt exception for this frozen recovery remains as recorded above.


---

## Lane disposition 2026-11-13 (p3-misc-b)

Not pursued in this lane: BLOCKED re-confirmed 2026-11-11 (lane boot23): frozen-worktree full-CLI SIGSEGV needs cargo/rustc + sanctioned full bootstrap. Not chaseable here.