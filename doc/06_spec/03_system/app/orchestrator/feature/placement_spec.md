# Placement scenarios

Source: `test/03_system/app/orchestrator/feature/placement_spec.spl`.
Status: **NOT_RUN**. Authored manual; not SPipe-generated evidence.
No admitted SSpec, native diagnostic or live-provider result is claimed.

Typed host inventory and resource profiles produce placement proposals only. The host must revalidate the selected ledger fence and capacity before committing any reservation.

The executable scenarios assert these behaviors:

1. Preserves GPU hosts for CPU work and publishes effective caps.
2. Queues below minimum and exposes the rejection reason.
3. Allocates between minimum and recommendation without increasing caps.
4. Rejects duplicate physical capacity and unsupported GPU sharing.
5. Never downgrades a required GPU claim to CPU.
6. Requires current authorization health and enforcement.
7. Rejects stale continuity and mismatched runtime eligibility.
8. Uses a stable host identity tie break independent of inventory order.
9. Binds the selected offer and attempt identity into canonical host intent.
10. Cannot construct a reservation for a queued or invalid selection.
11. Rejects unresolved devices or allocation and cap disagreement.

No result here implies a callable controller service, host mutation, authenticated
receipt provenance, provider execution or TaskRunner parent acceptance. These are
necessary dependencies for the actual signed dispatch composition. Runtime and
manual-generation checks remain pending an admitted runner and authorized build.
