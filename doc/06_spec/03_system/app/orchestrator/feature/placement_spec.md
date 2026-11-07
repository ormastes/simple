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

## Authored GPU admission coverage — 2026-11-07

Status remains **NOT_RUN / AWAITING_VERIFICATION**. This appended manual is
handwritten from two new executable examples, not generated execution evidence.

12. Across three inventory permutations and Prepared/Executing/Uncertain
    reservation states, `gpu-0` remains busy and exactly `gpu-1` is selected.
    The canonical reservation intent names that one device and independently
    expects 2000 millicores and 4000 memory bytes. Applying the existing pure
    host preparation transition leaves exactly `gpu-2` available. These are
    literal expected identities, not comparisons only against the computed offer.
13. Fully busy inventory queues for all three active states. An explicitly
    Released reservation permits selection again, with exactly `gpu-0` chosen
    regardless of its position after `gpu-1` in the inventory.

These tests exercise pure placement and host-ledger admission, not physical
device assignment or provider execution. No runtime/docgen was run; all later
builds and tests retain the shared five-CPU maximum.
