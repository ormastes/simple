# Collection analysis in the archived HIR route

The existing pre-monomorphization collection analyzer remains the semantic
owner. Its `CollectionPlan` contains original expressions, call arguments and
loop-origin blocks. Promoting `CollectionModuleAnalysisV1` would retain body
graphs after a module lease closes.

`CollectionArchiveAnalysisV1` instead retains the complete original archive
descriptor, exact registry source bytes, every typed registry binding, backend,
an input digest and scalar output counts. The capture executes the original
analyzer over a complete module inside one lease; only the descriptor and cache
diagnostic roots are promoted after pause. Success and error results are retained
before the lease ends. Complete plans never enter the descriptor.

The borrowed replay API verifies input identity, parses the exact registry source
through its existing owner, rebinds the original typed bindings, validates actual
function/symbol/signature/receiver/arity ownership, and runs the original analyzer
again. It returns complete facts, findings, plans and blockers only while the
caller owns an active unpaused lease. It opens/closes/promotes nothing. Its caller
must consume the result before reclamation and clear/promote the existing cache
diagnostic owner according to the shared borrowed-reader contract. Scalar replay
checks are consistency checks; they grant no callback or optimization authority.

The driver adapter checks complete ordered inventory, unique physical paths and
consistent selected provider before capture. Missing binding owners refuse.
Descriptors publish only after every module's binding validation and capture
passes. Both retained and archived analysis entry points clear the other route's
results, and reconfiguration discards both. The existing retained binding function
was moved unchanged into a shared module; its facade remains exported.

This adapter is inactive until the production archived pipeline calls it. No
native execution or memory qualification is claimed. Required native acceptance
includes genuine registered collection plans with callback and loop-origin body
parity, a binding-invalid later module refusing the whole publication, descriptor
and source mutation refusals, occupied/paused lease preservation, repeated replay
after scope churn, and switching retained/archived request routes. Empty-registry
parity alone cannot qualify those requirements. Full CLI/runner and the original
memory cap remain mandatory after activation.
