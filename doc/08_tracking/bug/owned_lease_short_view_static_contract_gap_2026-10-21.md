# Owned lease library views lack a checked compiler callback contract

Status: OPEN. AC-BOR-04 remains incomplete. Source inspection only; no checks
were rerun. Existing focused scalar lease probe PASS is retained unchanged.

## Accepted requirement and current evidence

The recovery plan section 3.2 requires an owned lease to retain permission while
each access creates a fresh short view. A short view cannot escape or cross a
suspension. AC-BOR-04 requires this without widening a borrow.

`std.nogc_sync_mut.ptr.lease` implements retained scalar WeakLease access,
epoch revocation on normal callback return, repeated fresh views, and cleanup
before propagating Result failures. It has no general storage pointer or
object lifetime implementation. WeakLease copies alias a single acquisition;
release is explicit and once-only. Its control block is not language unique
owner drop glue. LeaseView is an ordinary record of scalar registry identities,
not a compiler region-bound borrowed reference. Runtime revocation prevents
later reads; it does not prove the compiler rejects storing a short view.

## Compiler integration gap

The current source now includes a local definition validator in
`src/compiler/35.semantics/param_effects/callback_contracts.spl` for checked
synchronous callback slots. `infer.spl` and `short_escape.spl` consume the
validated contract at ordinary Call and StaticCall sites, including named
arguments; unknown imports fail closed. Transient `PeCtx` stores the admitted
symbol/slot table once and reports the validated contract to those consumers.
This is local nonescape proof source progress only; it has not been verified.

The local definition validator does not establish a fresh lease-view region,
carry a trusted contract through imported summaries/reexports, or provide
runtime object retention and compiler-generated lifecycle cleanup. A duplicate
symbol fail-closed repair is still under review. The presence of plain Named
LeaseView/WeakLease records does not supply those missing guarantees.

## Required acceptance proof

Introduce a definition-validated callback contract that survives typed import
summaries and aliases, then bind each callback parameter to its fresh access
region. Prove source acceptance of a long-lived owned lease with two sequential
short callbacks. Prove source rejection of returning, storing, capturing into an
escaping callback/task, or suspending with that view. Prove the owned token can
remain live across boundaries without keeping any view live. Establish actual
object retention and cleanup using the admitted compiler/runtime producer;
scalar registry tests alone cannot close this requirement.

Unrecoverable callback unwinding is separately tracked in
[the frontend cleanup gap](lease_view_exception_cleanup_frontend_gap_2026-10-21.md).
Atomic RC/Arc and cross-thread token/view transfer are separate unsupported
surfaces: the current weak/lease registry is single-threaded and does not claim
atomic ownership or race safety. Neither surface is marked PASS here.
