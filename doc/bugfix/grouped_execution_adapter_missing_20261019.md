# Missing grouped execution adapter source

REQ-IM-007. Base `4f62b79ec3b`; owner Astra feature acceptance; final reviewer
root's highest-model reviewer; sidecars N/A. Maximum three repair/check cycles,
initial implementation cycle one. Compiler execution is held by root.

`grouped_run.spl` and the retained `grouped_manager_main.spl` fixture import
`compiler.driver.action_graph.grouped_execution_adapter`, but that exact owner
is absent from tracked source. A path-specific history lookup across available
refs found no historical file. This is missing source, not an alternate provider
path discovered by the investigation. Three missing managed parse contract owners
are assigned separately; this adapter does not redeclare those transport types.

The restored interface uses existing `GroupedActionBindingV1`, lease and reap
contracts; `PackageCompileScheduleV1`; the canonical action coordinator; and
the artifact service bridge. It adds a dispatch record retaining the exact
publication lease at successful claim, attempt count and grouped lease. Ready
actions come only from `coordinator_ready_actions_v1`, not a new DAG scheduler.

Claims enforce declared idle slots and immutable bindings. Commits compare the
full retained dispatch identity, validate package publication boundaries and
pass the original publication lease to the bridge. Failures contain no artifact.
Recovery matches the full retained grouped lease and next generation, enforces
the bounded attempt count, stages canonical service/coordinator requeue, then
claims the replacement. Any failed transition returns the original owner state.
Successful independent peers are preserved.

The staging operation is extracted into
`demand_artifact_requeue_retired_v1` under the existing recovery owner. It is a
trusted serialized-parent transition, not death detection or an untrusted public
receipt verifier. The native proof-consuming recovery API still collects its
exact durable broker proof before invoking it. The grouped runner already
collects or replay-verifies that proof before adapter recovery; a caller merely
constructing a digest-shaped receipt has no process-death authority.

The grouped adapter's owner digest identifies a parent execution slot and epoch,
not an OS launch. Existing runner broker request/reap identity and journal remain
the OS authority. The earlier direct recovery API's full-launch owner binding
must not be confused with this adapter's retained slot binding. Full launch
dispatch-envelope journal integration remains separately planned.

Independent commit `8926f84271d` fixes the bridge's unconditional empty-output
guard so failed/cancelled action results can retire. Its separate spec checks
failure/cancellation, stale generation, duplicate retirement and empty success.

New modern SSpec and mirrored manual cover canonical readiness, typed absent
dispatches, worker bounds, exact retry, peer preservation, stale completion,
eight receipt mismatches, attempt exhaustion, final failure and forbidden
intermediate package publication. Runtime and docgen remain UNRUN. No Phase3,
live process retirement, or nine-feature completion claim is made.

Review cycle two corrects an identity-domain conflation: SCC identity is bound
to `schedule.variant_digest`; execution binding cache identity is bound to
`route.service.profile.compatibility_id`. Both are independently validated
digests and need not be equal. The shared spec fixture now uses distinct
identities, with positive claim and both-direction substitution negatives.
No digest domain is aliased and runtime qualification remains UNRUN.
