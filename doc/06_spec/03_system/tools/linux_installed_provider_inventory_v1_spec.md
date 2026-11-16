# Installed whole-provider inventory component

**Evidence: AUTHORED_NOT_RUN.** No runtime, native build, CLI engine or service
campaign was executed. The self-hosted runtime is unavailable and this session's
native iteration allowance is exhausted. This manual records authored behavior,
not a successful fixture, producer exclusion, absence, migration or admission.

Executable scenario: `test/03_system/tools/linux_installed_provider_inventory_v1_spec.spl`.
Data-only negative contracts: `test/01_unit/lib/container/linux_whole_inventory_http_v1_spec.spl`.

| Requirement | Scenario evidence |
|---|---|
| REQ-LINUX-WHOLE-INVENTORY-001 | Retained actual installed supervisor, root policy and one actual service incarnation |
| REQ-LINUX-WHOLE-INVENTORY-002 | Six unfiltered bounded resource queries, stopped and external containers included |
| REQ-LINUX-WHOLE-INVENTORY-003 | Native identities retained as quarantined rows; execution candidates refuse fresh compute claims |
| REQ-LINUX-WHOLE-INVENTORY-004 | Inventory cleanup invalidates aliases and preserves supervisor inhibition; no machine grant |

The administrator must prepare a disposable, real Podman **5.2.5** installation
with one dedicated rootless service UID. The root-protected supervisor profile
must explicitly install `closedProviderModel: single-rootless-uid-all-stores-pinned-v1`
and a canonical installed V3 `providerPolicy`. The real machine policy must name
exactly one `linux-podman` provider whose embedded CLI policy matches byte for byte.
Alternate UIDs/stores/providers are outside this initial model and refuse
completeness. The closed store universe is an administrator obligation, not an
observation derived from a list of endpoints supplied by the caller.

Before starting the fixture's real supervisor MainPID, prepare unowned **stopped**
containers (including an external storage container), stopped pods, images,
volumes, networks and secrets. The scenario requires at least one row in every
class. Resource labels or Host/service scope must not establish ownership.
Do not create resources inside the scenario or substitute a scripted engine,
synthetic peer, JSON observation or fake supervisor. A missing fixture fails;
there is no unsupported-host skip or success-shaped fallback.

1. Open the actual installed supervisor and retain its real inhibition owner.
   Its MainPID, process namespace and provider service incarnation must validate.
2. Open inventory from that owner. A separate protected policy reader must
   reconcile the exact installed one-provider store universe. Each native Unix
   connection must match the real provider MainPID, UID and retained socket
   identity; every exchange rechecks actual exclusion before and after.
3. Query containers with `all=true&external=true`, images with `all=true`, and
   pods, volumes, networks and secrets without filters. No label, Host scope,
   latest/page/limit/since/before restriction is permitted. Consume each response
   through native EOF, exact HTTP framing and strict bounded JSON.
4. Check all six classes retain their class and native identity. Containers and
   pods produce `ExistingExecutionQuarantined`; all rows remain quarantined.
   `CompleteInventory` would mean only that the six queries completed, even when
   noncompute objects exist. Default networks receive the same treatment as
   every other network and are never discarded by name.
5. Check exact supervisor generation, process identity, native peer/incarnation,
   service store digest and query/response digests. A fixed 30-second monotonic
   collection budget, 1 MiB JSON body, 2,113,536 bytes per HTTP response,
   12,681,216 bytes for the six list responses and 4,096 aggregate rows apply.
   Two separately bounded `/info` exchanges make the total transport bound
   16,908,288 bytes. Limits/truncation/parsing uncertainty are `Incomplete`;
   stream, native identity or continuity failures are `Unknown`. Neither can
   become emptiness. A stale owner produces an error, never consumption proof.
6. Close only this inventory reader/socket. A copied alias becomes stale and
   actual supervisor inhibition remains retained for its upper owner.
   `cleanup_diagnostic_v1()` remains readable after inventory close. An explicit
   native reader `consumed-error` clears that consumed reader exactly once;
   generic stale/foreign/retained responses keep it pending. A native socket
   close requires `closed=true` plus no returned owner to establish consumption.
   Sticky cleanup errors remain in the final `consumed-error` disposition and
   its diagnostic across retries. Data-only lifecycle contracts are authored;
   native consumed-close fault injection is **NOT_COVERED / NOT_RUN**.

Provider in-flight requests, internal asynchronous work and quiescence/drain
**remain unproved**. Existing native containers/pods are never adopted or deleted
from labels. Images, volumes, networks and secrets remain explicit unresolved
storage/endpoint obligations. No inventory observation consumes the shared
writer, accounts old charges, settles absence or admits machine genesis.
`provider_drain_proven` and `machine_genesis_admitted` remain false;
`unresolved_storage_and_endpoints` remains true. The exact shared-writer
successor and migration handoff belong to the upper owner.

Pinned source inspected through the connected GitHub file reader at tag
`v5.2.5` in [Podman](https://github.com/podman-container-tools/podman/tree/v5.2.5):
`pkg/api/server/register_{containers,pods,images,volumes,networks,secrets}.go`,
`pkg/api/handlers/libpod/containers.go`, `pkg/domain/entities/types/container_ps.go`,
`pods.go`, `images.go`, `secrets.go`, `libpod/define/volume_inspect.go` and
`vendor/github.com/containers/common/libnetwork/types/network.go`. They establish
the exact request routes, `all`/`external` support and case-sensitive identity
keys (`Id`, `Name`, `id`, `ID`). Source inspection does not qualify runtime wire
behavior or a real closed installation.
