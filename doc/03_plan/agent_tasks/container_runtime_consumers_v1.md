# Container runtime consumer closure

Status: source dependency plan, 2026-11-08. No end-to-end or native qualification
is claimed here. Linux uses Podman; Windows uses Windows Docker process
isolation. Application consumers use the Simple Container API.

## Existing executable source paths

`src/app/orchestrator/command.spl` routes `dispatch`, `resume-execution`, and
`inspect-execution` to `execution.spl`. That module calls the existing
`controller_dispatch_v2` / `controller_inspect_execution_v2` functions in
`src/lib/nogc_sync_mut/orchestration/controller_dispatch_owner_v2.spl`.
The finite controller owner already retains its assignment journal and calls
`host_local_command_v1` for status, validation, preparation, execution and
inspection. Host owns a separate capacity/operation journal and invokes the
common Container owner. These source paths are present; a completed public
workflow still requires the concrete consumers and evidence below.

## Ordered implementation and acceptance

| Order | Owner and source | Concrete completion condition |
|---|---|---|
| 1 | Common terminal owner, Podman primary provider, daemon input owner | Actual primary eligibility/open, controlled native input latch, opaque single-owner session, cancellation-free reap collection. Preserve every failed-acquisition owner. Geometry and exec channels remain distinct. |
| 2 | Caret pane/service and Host helper owner | Typed primary adoption retains the canonical owner in the pane even on post-publication failure. Distinct primary helper archive/consumption/settlement uses the original signed helper chain. No output-follow receipt is relabeled. |
| 3 | Common control owner and actual Caret issuer | Consume the checked current Input/Geometry lease against actual adopted target. Input frame progress and native write attempts remain distinct; unknown accepted prefixes cannot be resent. Revocation acknowledgement requires the native barrier. Geometry requires an actual exact-target provider operation. |
| 4 | Host execution consumer and controller dispatch owner | Use the existing independent journals and retained signed assignment chain. Preserve controller and Host cleanup owners across all responses. Resume uncertain effects by exact retained identity; never repeat create/start from a transport error. Persistent responsiveness requires staged native effects, not a synchronous callback labeled asynchronous. |
| 5 | Runner/AgentSession producers and Host workspace owner | Wire real parent-verified result production, actual image/CLI probe evidence, protected workspace/storage preparation and exact execution identity. A declared digest, selected-user string, or metadata receipt cannot replace observation. Audit and update the existing consumers rather than add another scheduler or journal. |
| 6 | Root qualification owner with platform leads | Allocate bounded real workflow checks only after source dependencies close. Verify public dispatch, parent result verification, exact inspection/resume, input/revoke/geometry, cancellation/cleanup and resource settlement on the supported platform profiles. Authored but unrun scenarios remain NOT_RUN. |

The Windows broker requires the actual deployment/completed-install/access
producer and authenticated effect channel. A raw Job lease, decoded frame or
read-only Engine observation does not supply that authority. Its session must
use a distinct real Windows owner; no fabricated Linux process reference.

## Holds and ownership constraints

The configured Podman containment association is held at its six-cycle limit
pending the user's explicit exception. Kernel-profile observations neither
repair nor waive that hold. An empty cgroup snapshot or missing container
object cannot discharge unknown contained exec work. Host's charge guard
remains until qualified provider evidence or the separate proven no-BEGIN
path is available.

The completed Podman exec-owner repair campaign is not reopened. New primary
attach source is a separate capability and leaves its owner/record files
unchanged. Source review of each new scope is bounded; green checks are not
repeated. No new build or native campaign is authorized by this plan.

Root owns integration and physical-check allocation. Common/Caret/Host/provider
leads review their actual producer-consumer boundaries before root lands a
dependency-complete source bundle. A merged source checkpoint is not a claim
that the full workflow passed.
