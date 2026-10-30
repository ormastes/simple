# mux_client_v1_spec

STATUS: NOT_RUN. 9 authored cases,0executed,0runtime passes.
Manual authored from current SSpec source; native docgen has not run.

Source: `test/01_unit/lib/nogc_sync_mut/sosix/mux_client_v1_spec.spl`.

Production config/deadline/admission/recovery helpers and early client refusal. No network operation qualifies a provider in these controls.

## Authored cases

1. requires explicit literal loopback and bounded configuration
2. does not create resources or claim a lease at construction
3. refuses CreateOwned and other backends before network I O
4. never manufactures an idle heartbeat without an issued lease
5. uses a single elapsed budget and rejects backwards or expired clocks
6. bases lease intervals on request start without overflow
7. retains bounded cleanup disposition for late and over-request issued connections
8. keeps recovery transport usable when rejected peer limits are below minimum
9. does not retain foreign or malformed connection identities for cleanup

## Visible steps

- Refuse discovery remote hosts wildcard and malformed auth
- Construct only explicit transport configuration
- Reject unsupported admission without a fallback
- Require the owner issued lease before maintenance
- Bound deadline arithmetic across fragmented I O
- Check conservative lease and recovery interval bounds
- Separate correlated cleanup retention from full admission
- Select safe request budget for cleanup instead of rejected negotiation
- Require the original namespace backend and valid owner incarnation

## Admission and evidence

Use only an admitted current Phase3 compiler and matching runtime/full modern
SSpec runner with semantic --library-mode nogc-sync-mut and generic library roots.
Do not select a family by --source directory, use a seed, rebuild Phase2 for this
suite, or accept missing framework imports as a passing run. No exact executable
or invocation is admitted by this source checkpoint.

Retain producer/source/runtime hashes, actual argv, stdout/stderr, exit status,
case totals with failures/blocked/unrun, resource peaks and cleanup receipts.
Auth tokens and pane content are excluded from diagnostic errors and public reports.
Private expected fixture text is inspected only by assertions/owned artifacts.
All current cases remain NOT_RUN; source checks are not native test evidence.
