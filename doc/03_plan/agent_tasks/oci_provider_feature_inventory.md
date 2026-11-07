# Linux OCI provider completion inventory

The user resumed implementation of all features from release
`862d9e361534c1a13f83a2f43da06e07847df5af`. This inventory preserves remaining
work; completing the first output attachment does not complete the provider.
The subsequent explicit requirement is Linux Podman and Windows Docker through
the common Simple Container API. Platform commands stay in provider owners;
Host, Caret, and runners consume the common API.

| Capability | Current source boundary | Remaining implementation/acceptance |
|---|---|---|
| Explicit Podman selection | Merged CI selection; no silent Docker fallback | Live unavailable-engine and explicit compatibility matrix |
| Request retention/replay | Canonical request codec, V2 payload-bound intent, V1 reconciliation-only migration | Executable real-journal regression and restart matrix |
| Command/ENTRYPOINT | Merged typed executable override and CI request mapping | Live image ENTRYPOINT/CMD matrix |
| Engine identity/scope | Merged explicit trusted-admin mutable-path policy, UID/store/hash observations | Actual Host signed-enrollment consumer and live continuity matrix |
| Common lifecycle API | Linux adapter decodes the retained request, checks full scope/digest, and routes actual lifecycle/read/recovery operations | Aggregate dependency integration, real Host consumer, executable cross-platform matrix |
| Launch deadline | Common action/request/operation binding and Linux managed route authored | Captured native owner checks after governor and before exec; actual native tests; expiry never kills an admitted workload |
| Absence proof | Independent exact-ID Podman container-exists query and common receipt mapping authored | Receipt binding tests and live independent object-absence oracle; separate from helper reap and Host settlement |
| Output attachment | Provisional provider session work remains isolated, not admitted as complete | Full group-owner bundle, exact running native identity, policy correlation, one helper, common stream API, same-process smux adoption, nonce observed by sole pane reader |
| Helper lifetime | Daemon owns canonical generation-bearing process/group lifecycle repair | Pre-spawn cleanup capability, safe rollback, close retention, stale-reference rejection; no raw PID fallback |
| Terminal input/TTY | Request digest/codec has explicit modes; provider effects reject them | Actual create stdin/TTY flags, interactive transport ownership, input backpressure, detach behavior, separate readiness evidence |
| Terminal resize | Output-only smux transport refuses geometry changes | Backend resize capability and exact execution identity authorization; no local PTY resize proxy claim |
| Exec sessions | No admitted integrated provider exec owner | Exact parent runtime identity, immutable exec request/receipt, independently owned stream and exit lifecycle |
| Environment | Explicit bounded entries now map to typed --env NAME=VALUE; new Podman creates disable implicit host proxy inheritance | Common signed-consumer integration and literal-value live oracle; image/admin configuration is not claimed empty |
| Working directory | Explicit canonical absolute cwd maps to --workdir and exact common action projection | Common facade integration and live image-path behavior through authorized consumer |
| Workspace/storage | Existing build-input/output mount mode is separate | General workspace attachment policy, immutable source/destination/mode binding, scoped ownership and cleanup; no global prune |
| Statistics | Existing provider returns explicit unsupported result | Exact scoped native collection, typed units/limits, authorization and independently observed metrics |
| Full vertical authorization | Host/orchestrator/Caret own their composed consumers | Signed controller→host execution and authenticated binding; no remote argv/root/ref authority |

Provider ownership: Astra Podman with one Sol worker. Daemon owns native process
registry/group lifetime; Caret owns authenticated smux composition and pane I/O;
Host owns installed policy, durable enrollment/reservation/request resolution;
orchestrator owns signed dispatch and immutable target-bound replay. Root owns
landing coordination and the aggregate five-CPU allocation (`taskset -c 0-4`).

All prior executable qualification gaps remain explicit. No compiler retries,
package installations, or live Podman claims are authorized by this inventory.
The current adapter, deadline, native uname, and absence specifications are
AUTHORED_UNRUN. No full feature, runtime, or production-readiness PASS is implied.
Specs must exercise the production owner entrypoints; mocks and scripted seams
are unit evidence only. The live provider→smux spec is separate from the full
controller/Host authorization acceptance and cannot stand in for it.
