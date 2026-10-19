# Bounded production transitions and weighted work

Executable: [build_cache_bounded_model_spec.spl](../../../../test/00_formal_verification/compiler/build_cache_bounded_model_spec.spl).

Status: the original service/cost scenarios retain their recorded bounded Phase 1
pass. The recovery refinement and projection negatives added on 2026-10-19 are
**AUTHORED_UNRUN**. The changed file has not been executed or regenerated with
SPipe/docgen; this manual was updated by hand. This is finite-domain checking,
not a universal theorem or measured hardware performance claim.

1. Enumerate all 192 combinations of owner, lease identity/generation, result
   action, snapshot, success and cancellation. Call the real completion owner.
   Unauthorized inputs preserve the current lease; only an authorized coherent
   success publishes an artifact.
2. Enumerate all 625 four-event traces over two claimers, two completers and
   cancellation. Call the production service each time. Count actual execution
   authorizations and publication transitions; each remains at most one.
3. Reapply 16 claims while the current lease never completes. The actual service
   retains the dead owner's generation when no admitted retirement is supplied.
   The separate proof-gated recovery API exists; retrying claim alone is not
   recovery or a successful liveness check.
4. Enumerate 512 bounded weighted cold/warm work configurations. Account for
   capture, enumeration, hashes, reads, header decode, parse/HIR/MIR work,
   objects, links, startup, scheduler and receipt work. A doubled parse and a
   per-target scan have explicit additional cost; warm admitted reuse still
   pays decode/startup/scheduling cost. No count is called milliseconds.
5. Start from a real generation-7 bridge claim, then enumerate all 625 depth-four
   traces over admitted retirement, successor claim, old completion, successor
   completion and cancellation. At each of 2,500 prefixes, compare production
   acceptance, service/coordinator state, original/successor authority, retained
   lease, publication and reservation with an independent abstract transition
   table. Recheck the prior input projection after each owned-return operation;
   cancellation explicitly mutates its local route and has no acceptance boolean.
   Count starts from actual pending-to-running transitions (at most one per generation) and
   publication transitions (at most one overall). Retirement's collected-tree
   admission is an explicit external precondition: this scenario creates no
   broker receipts and launches no processes.
6. Change the lease generation, artifact digest and reserved memory separately
   in an initial route. Require the projection to report the exact wrong field;
   the original route must still match its initial model.

Cancellation requests preserve a running task's token and reservation; they do
not prove that its process has terminated. Cancellation after completion sets
the coordinator cancellation latch without removing the published artifact.
Repeated recovery, repeated claim and stale/duplicate completion reject without
changing the modeled ownership state.

| Requirement | Source scenario | Boundary |
|---|---|---|
| REQ-FORMAL-BOUNDED | 192 inputs, original 625 traces, new 625 recovery traces, 512 cost configurations | Enumerated domains only |
| REQ-FORMAL-OWNER | Recovery trace projection and three mutation negatives | Reap admission assumed; no live owner death proof |
| REQ-IM-007 | Epoch fencing, cancellation, one publication, reservation accounting | One action, generations 7 and 8, depth four |

<details>
<summary>Recovery scenario assertions (source-authored, unrun)</summary>

```simple
it "should refine all 625 admitted-recovery traces against the independent state model":
    step("Claim generation 7 and enumerate four events over recovery, successor claim, both completions and cancellation")
    step("Compare acceptance and both owner states at every prefix while preserving the input value")
    expect(bounded_recovery_traces().unwrap()).to_equal(625)
```

`bounded_recovery_model_step` contains the independent table;
`bounded_recovery_projection` checks observable fields; `bounded_recovery_traces`
invokes existing production owners. Projection negatives require `lease fence`,
`publication` and `reservation` respectively, not generic successful execution.

</details>

The trace checker observes production service transitions. The weighted counts
are a proposed accounting model, not instrumented compiler work. A successful
bounded run cannot promote `FormalStatus` to `ModelProven`, `SourceRefined` or
`ArtifactVerified`.

Design and exclusions: [bounded recovery refinement](../../../05_design/build_cache_bounded_recovery_refinement_20261019.md).

Evidence/report: [formal verification report](../../../09_report/build_cache_formal_verification_2026-10-10.md).
