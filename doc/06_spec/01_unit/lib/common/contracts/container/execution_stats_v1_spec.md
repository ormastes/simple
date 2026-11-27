# Typed container stats observation shape

Source: `test/01_unit/lib/common/contracts/container/execution_stats_v1_spec.spl`.
Status: **AUTHORED_NOT_RUN**; manually authored, docgen not executed.

These six cases call production shape validators with explicit DATA fixtures.
They do not construct a genuine container owner or claim that accepted DTOs are
native evidence, admission, resource-limit enforcement or accounting release.

1. Accept observed CPU zero alongside explicit unsupported I/O and an ordered
   positive monotonic read interval.
2. Reject zero/nonpositive or decreasing observation time; equal endpoints are
   allowed because the bracket is not a measured sampling resolution promise.
3. Reject inconsistent provider generation and scope/incarnation attribution.
4. Reject missing request/subject digests and an unrecognized source claiming
   CLI CPU percentages or memory working-set semantics.
5. Reject negative counters and permission failures mislabeled unsupported.
6. Require a bounded, consistent I/O collection; an empty device collection
   cannot contain nonzero aggregate traffic.

No spec/compiler/native/runtime execution occurred. Shape validation neither
proves a simultaneous multi-file snapshot nor grants a caller access to original
cgroup handles. The actual owner-produced observation remains a separate full
path requirement; this independent leaf is held until that path is reviewed.
