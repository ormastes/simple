# Windows server discovery/NAT V6 regression manual

Status: **AUTHORED_NOT_RUN**. No Windows native binary, Docker, HNS, network,
DNS, firewall or remote-server connection was executed. Scripted facts do not
qualify native behavior. Executable mirror:
`test/01_unit/lib/nogc_async_mut/container/providers/windows/docker_server_network_v6_spec.spl`.

Reproduction: Windows native requests previously had no workload environment
and their provider always passed `--network none`. A public server snapshot
could neither reach the launched process nor authorize actual connectivity.
The new pre-sign producer binds a minimal public discovery triple; provider
request V5 carries it, while V6 additionally selects only an installed exact
pre-existing NAT network. V1–V4/default-none records retain legacy behavior.

Authored assertions cover legacy field omission/argv; policy V3 and request
V5/V6 canonical roundtrips and downgrade refusals; request digest changes for
selected snapshot; exact native `--env`/`--network`/ENTRYPOINT argv including
spaces, empty values, shell-like text and one-word/JSON-looking executables;
case aliases, missing clear, NUL, size and secret-env rejection; name/host-network
fallback refusal; actual network observation mismatch, wrong driver/scope and
internal networks; extra/missing/foreign attached IDs; successful finite and
bounded cooperative scripted lifecycle; pre-effect refusal; and post-create
failure retaining the exact candidate ID/unknown intent.
Actual effective reserved-environment assertions reject image case aliases,
duplicate/missing values and an unexpected config path, including a scripted
provider failure that retains the created native ID before any started claim.
Cleanup-only source assertions then remove that retained ID despite unready
environment, require actual exact-ID absence, reject unrelated IDs or changed
operation/scope proof, and refuse deriving cleanup authority from preparation
without a retained create birth. This path never authorizes start/admission.
R2 adds direct `recover` entry regressions: matching attached IDs cannot bypass
actual driver/name/internal-network checks; genuinely ready recovered objects
keep strict cleanup; forged recovery metadata cannot use relaxed cleanup when
effective environment becomes poisoned. Actual-create provenance is a private
capture-derived bit, never a field imported from the caller's intent.

Restart handoff of a genuine archived create birth is not implemented. Host
archive metadata alone cannot supply that grant; poisoned recovered objects
retain charge/custody until a real protected archive handoff exists. Stop may
act then return blocked after strict post-stop readiness failure; destroy still
requires its independent exact-ID absence result before completion.

Native qualification requires an actual administrator-approved network ID/name,
matching Windows engine/image versions, and installed public server endpoint.
The running container must select the projected endpoint rather than an image's
inherited config path and complete the intended server connection. Inspect
actual network properties and exactly one attached NetworkID, then inject stale
IDs, wrong driver/internal networks and interrupted post-create inspection.
Every uncertain created container must retain its exact recovery/cleanup owner
and Host charge. No global network/container prune is an acceptable cleanup.

Docker versions that defer reporting NetworkID until start fail the strict
post-create proof in this source implementation; this must be measured before
claiming a supported host/image/engine matrix. NAT is not proof of external
reachability, authentication or egress restrictions. Secret references require
their separately authorized resolver; this feature never mounts private keys.
