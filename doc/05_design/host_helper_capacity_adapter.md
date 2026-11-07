# Helper capacity uses the existing host ledger

The normal reservation API retains its strict `host_reservation_v1` action.
Separate helper entrypoints require `host_helper_reservation_v1`; consuming a
prepared helper requires `host_helper_execute_v1`. Only the authorization query
derives that execution action. The immutable original operation is never
relabelled in the journal or receipt digest.

`host_capacity_owner_prepare_helper_v1`, `begin_helper_v1`, and
`prepared_helper_receipt_v1` are trusted internal capacity primitives, analogous
to the existing normal owner APIs. They do not replace signature verification.
Helper CPU and memory must both be positive. The helper reservation is a separate
row in the same physical capacity projection, charged alongside its parent and
all other workloads. There is no second scheduler or helper capacity ledger.

Projection recognizes the exact normal/helper actions independently per retained
row. Trusted expiry can cancel an unconsumed helper preparation using its exact
receipt. Executing/outcome-unknown helpers remain charged; closing a pipe, losing
a response or reaching an authority deadline never releases those resources.

The host helper service consumer must verify current dual-role signatures, the
signed aggregate `ControllerParentBudgetV1`, immutable parent assignment and
retained host operation, current scope/epoch, and the sum of parent plus ALL
retained helpers before invoking these primitives. It must commit execution
intent before issuing a nonserialized lease to the actual helper owner. Exact
native group-reap/cgroup-empty evidence and a durable host acknowledgment are
required before effectful helper resources can be released. Those consumers and
settlement paths remain separate ongoing implementation work.

Three authored cases in `host_signed_prepare_spec.spl` cover action separation,
expiry versus consumed state, mixed normal/helper reopen and nonzero budgets.
All are **NOT_RUN**. Source review is not native execution qualification.
