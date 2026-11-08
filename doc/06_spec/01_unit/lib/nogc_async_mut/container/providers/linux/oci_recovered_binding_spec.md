# Durable recovered OCI request binding

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_recovered_binding_spec.spl`.

Status: **AUTHORED / UNEXECUTED / AWAITING_VERIFICATION**. The cases select the
real canonical journal writer with explicit scripted engine observations. No
native container, policy observation, filesystem durability experiment, or
executed passing result is claimed.

1. A malformed whole create response triggers exact identity inspection. A
   verified full native ID and matching labels are published as V2 before
   recovery succeeds. Reconstructing a managed provider from that actual journal
   retains request digest and operation ID and permits a dedicated exact-ID
   absence query without changing the stored bytes.
2. A conflicting retained native identity cannot be overwritten by recovery.
   An earlier identity guard or the publication guard must refuse success and
   preserve prior authority. Multiple records, wrong native/operation identity,
   and changed request payload likewise refuse; a payload mismatch is rejected
   before the command executor is called.

Fixtures reuse the shared request/directory/read helpers and exact routed
command fixtures. `persist_scripted_journal=true` exercises native filesystem
publication, reread, and directory barrier source paths when eventually run.
It never turns the synthetic engine observation into native qualification.
The uncertain-publication branch remains source reviewed where a safe
nonblocking filesystem failure oracle is unavailable; no lock-wait fixture or
fake passing assertion substitutes for such evidence.
