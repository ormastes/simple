# Per-module ABI receipt scratch survives HIR lowering

Status: candidate fix; native regression pending admission. Baseline:
`5742353e64`. This is not yet established as the cause of the test-runner
memory stop near module 465.

`driver_hir_pipeline_lowering.spl` computes an ABI digest for each completed
module after the transient lowering scope has ended. The ABI encoder builds
canonical rows, sorts text, and hashes the encoded interface. Its result is
only a digest or diagnostic; the intermediate arrays and text have no later
consumer. The native heap registry retains unscoped allocations, so those
intermediates accumulate across modules. Disabling phase output does not avoid
the digest computation. HIR cache publication already scopes its own encoder
and does not reclaim this separate work.

The candidate driver helper acquires a transient scratch scope, calculates the
unchanged digest, pauses and promotes only `Result<text, text>`, then closes the
scope on both encoder success and error. Logging remains outside the scope.
Acquisition failure returns an advisory error without closing an enclosing
owner's scope. No memory caps, retained HIR semantics, codec format, or digest
algorithm change.

The focused spec is
`test/01_unit/compiler/driver/hir_abi_interface_scratch_spec.spl`. It checks
digest and dynamically generated error lifetime, nested-owner preservation,
and native heap-registry growth against the original unscoped calculation.
An interpreter result alone cannot prove native reclamation. Native validation
and the larger phase build remain outstanding; no memory reduction is claimed
until measured.
