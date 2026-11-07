# Controller workload fence scenarios

Source: `test/03_system/app/orchestrator/feature/controller_workload_fence_spec.spl`.
Status: **NOT_RUN**. Authored manual; not SPipe-generated evidence.
No admitted SSpec, native diagnostic or live-provider result is claimed.

Compose a pure placement proposal through immutable intent and assignment binding into a workload fence. Cancellation stays sticky; uncertain assignments cannot be replaced by a timeout or another proposal.

The executable scenarios assert these behaviors:

1. Binds one immutable assignment and refuses stale first bind.
2. Retains uncertain assignment until evidence checked retirement exists.
3. Keeps cancellation sticky before and after binding.
4. Matches controller envelope identity and rejects payload or policy tampering.
5. Restores only exact canonical immutable intent and envelope objects.
6. Rejects scope changes generation skips and revision overflow.
7. Round trips canonical fence and rejects invalid or ambiguous wire records.
8. Admits only create first bind and sticky cancel replay transitions.
9. Composes placement intent and immutable binding into the workload fence.

No result here implies a callable controller service, host mutation, authenticated
receipt provenance, provider execution or TaskRunner parent acceptance. These are
necessary dependencies for the actual signed dispatch composition. Runtime and
manual-generation checks remain pending an admitted runner and authorized build.
