# Owned Host execution producer V3

Status: **AWAITING_VERIFICATION / AUTHORED_NOT_RUN**, 2026-11-14. This package
follows the frozen Windows Host foundation. Its eight native export proposal
is unchanged; the closed runtime campaign has not restarted.

## Execution and ownership

`HostWindowsLocalRootV3.execute_v3` invokes the existing signed
`host_authorized_execute_v2`. The executor retains the original packet, common
plan and request before committing `executing`. The common Container API then
creates the container; its exact creation identity is retained before start.
Start and inspect return the current Container owner. Running or inspected is
not workload completion, and unknown effects keep their reservation charged.
An executing/outcome-unknown row cannot replay create.

The root retains both returned owners before any post-effect validation or
response encoding. Windows archive, intent and observation storage uses the
actual journal capability with immutable publication/readback. Paths and codecs
remain unchanged. Linux preserves its prior fsync publication behavior. Windows
privacy is native ACL/retained-directory evidence, never pathname mode bits.
The durability profile remains process-crash-v1, not power-loss durability.

After begin, the authorization callback cannot check the old WAL revision:
begin has deliberately advanced it. Instead it revalidates the actual protected
deployment and originating native journal store, native liveness, exact writer
lease bytes, policy and clocks. The executor owns its updated journal separately.
Changed policy, closed/replaced writer and expiration fail closed.

## Lower authority bridge

Authorization context is a common data contract, publicly re-exported by the
capacity module. Enrollment no longer imports execution ownership solely to
name it. The parallel Windows lane extracts read-only provider observation away
from the effect exchange dependency graph.

The actual store factory records its private origin-root generation.
`belongs_to` checks that exact generation and liveness. A consumption receipt
similarly correlates to its issuing store, so equal bytes from another authentic
store cannot authorize this journal. No raw token getter or new native export
is added. The lower connection verifier remains responsible for independent
signed admission and exact retained parent/helper runtime provenance.

## Consumers and dependencies

`host_service_domain_effect_turn_v3` is an explicit effect-worker port for both
platforms. It checks the requested operation ID, invokes the shared executor,
and retains the updated domain before response encoding. The nonblocking
control callback continues to refuse execution. The generic finite CLI selects
the explicit port for `host-execute`; `host-parent-budget` consumes the parallel
lane's owned signed-budget publication hook.

Windows obtains a new incarnation on each service start. Separate finite CLI
prepare/execute invocations therefore cannot preserve a reservation's scope and
correctly refuse that sequence. The parallel generic smux V5 owner must retain
the same domain across status, signed prepare and signed execute, and dispatch
execution from its effect worker. That persistent wiring is required acceptance,
not established by finite command syntax. Checked stdin currently refuses
Windows; no raw diagnostic-input bypass or new stdio transport is introduced.

The observation facade and owned parent-budget APIs are coordinated cross-lane
dependencies. This package must be reviewed with them before landing; it is not
a standalone complete Windows orchestrator implementation.

## Evidence

Four authored scenarios use actual journal/signature fixtures with explicitly
scripted Linux provider effects: packet/intent/observation retention, conflicting
archive refusal before begin, post-create uncertainty with replay refusal, and
production path/CLI guards. One added native Windows fixture scenario checks
origin/receipt correlation across two real protected roots. All are **NOT_RUN**;
manuals are authored and not docgen-verified.

Successful configured Windows execution; changed authority during effects;
post-effect publication/cleanup failures; restart recovery; persistent daemon
dispatch; and performance remain **NOT_COVERED / NOT_RUN**. Existing signed
executor deadline/replay/failure specs remain required regression inputs. No
coverage percentage, native success or complete Windows acceptance is claimed.
