# MIR declaration repository seal ownership

Status: candidate repair; focused and production verification pending.

The admitted attempt 6 compiler completed final mono issuance and consumed its
repository, then failed with `MIR declaration repository integrity failed` in
the focused VMM route. The retained log is
`/tmp/simple-release-1.0.0-phase2-attempt6-vmm-mono-evidence-20261029/attempt/vmm/build.log`
(SHA256 `cd59f60986cb43e68b85a3b030e6ba9410d0338cba2da65b4d68d0e0c97a2f6f`).
The bounded attempt ended with timeout 124 and no object. That combined message
does not establish which validity, pause, promotion or scope-end predicate failed.

At release baseline `8e98695970a813def06ed8ea57fc2276bd20e27c`, the declaration
factory still constructs `MirHirDeclarationRepositoryV1` before its seal scope,
then promotes that external root after assigning the scratch-owned authority.
The candidate starts the existing scope before construction. It retains every
integrity and ownership gate, closes the scope before reporting any failure,
and includes all four scalar predicate results in that error. No fallback or
publication on failure is introduced.

The focused probe uses the actual declaration carrier, rather than a structural
copy. It compares refusal of an external root against retention of a scoped root
whose context, source-order array and declaration map predate the scope. The
probe does not issue a real repository, validate declaration contents or replace
the required production VMM regression. Its empty declaration map is ownership
test data, not an admitted production inventory.

Production acceptance requires the rebuilt producer to pass the original owned
archive route's declaration seal and advance through its actual consumers. Any
remaining failure must retain the new predicate diagnostics and its independent
terminal status. This candidate does not claim full CLI, runner or release
qualification.

## Retained producer probe limitation

The first actual-carrier probe build used admitted attempt 6 producer
`72b21f6a771c5df38094af04863f9354328d8f95de0406dec641ac08e733a06d`
with independently recorded target inventory
`efd3050736214c638d4ce06138dec0123d07e320a794cb7c3dd84fe1ff196020`.
It stopped before producing an executable: 206 HIR modules completed and 191
remained BLOCKED, with zero CRASH rows and build exit 1. Evidence is retained at
`/tmp/simple-mir-declaration-scope-probe-20261030`; source and authority
immutability checks passed. The probe has not executed, so this is not evidence
for either promotion outcome. Qualification requires a producer that can compile
the actual declaration carrier's dependency closure.
