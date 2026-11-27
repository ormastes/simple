# Windows container server discovery and explicit NAT selection

Status: **AUTHORED_NOT_RUN**. This is provider source implementation and authored
specification, not Windows/engine/network qualification. Base source is release
commit `981a3475443cdf5bdface1c501a561663cb2f832`.

The shared pre-sign producer selects the minimal public server snapshot, injects
`SIMPLE_SERVERS_SDN`, `SIMPLE_SERVER_CLIENT_SCOPE=container` and
`SIMPLE_SERVERS_CONFIG=` into the unsigned native request, then derives its
request digest, retained bytes and common Container execution plan. The third
entry clears an image-inherited discovery path and is itself bound before
signing. No signed plan is rewritten. Authentication/trust references stay
public references; no secret bytes, host home, key store or runtime socket is
mounted or inherited. The Windows provider admits only this exact reserved
triple, rejecting case-folded aliases/duplicates, NULs, oversized values and
conflicting/non-public snapshots through the shared validator. SDN punctuation
and newlines remain literal bytes within one typed `--env` argument.

Wire compatibility is explicit: policy V1/V2 and request V1–V4 retain their old
bytes and argv when new fields are absent. Nonempty environment selects request
V5. Non-`none` networking selects V6 and binds the selected network and installed
network policy fields as well as the environment. Default `none` is preserved.
V5/V6 clear image ENTRYPOINT and pass the complete command after IMAGE, preserving
executable bytes, spaces, empty arguments and one-word commands without shell
concatenation or Docker's ENTRYPOINT JSON interpretation. Legacy argv is unchanged.

Trusted policy V3 adds paired `network_id`/`network_name`, defaulting empty. The
ID is a complete lowercase 64-hex engine ID; the name is bounded and compared
exactly. A non-`none` request may select only that ID. Public server configuration
cannot authorize a network. Before prepare/create/start inspection, the actual
retained Docker provider queries the installed network and requires its exact
ID/name plus `nat`, `local`, and `Internal=false`. The shared finite/cooperative
reducer performs these stages without a blocking inspection in the event loop.
After create/start it rechecks engine/network identity and validates exactly one
container-attached NetworkID. Missing, extra or mismatched attachments cannot
produce success. Policy origin equality and common adapter request decoding
include the new fields through existing canonical policy/request codecs.
Direct recovery/readiness observation performs the same actual network-policy
probe before its attached-ID/environment checks; it cannot adopt a container
solely because its attached ID matches while the observed driver/name/scope or
internal-network status disagrees with installed policy.

For discovery requests the same finite/cooperative reducer also inspects actual
reserved `Config.Env` before start or a created/running success. A fixed Go
template selects only the three reserved keys using case-folded matching, then
emits bounded JSON with the exact native ID. The validator requires canonical
uppercase names exactly once and byte equality with all three signed request
values; mixed-case image aliases, duplicates, unexpected config paths and
missing entries fail with the candidate ID retained. No unrelated image secret
environment is emitted or logged. Legacy empty-environment requests skip this
stage. The stage precedes the existing full ownership/isolation inspection, so
it adds no fabricated completion or pending state to the public progress carrier.

Only an existing administrator-provisioned network is selected. No network is
created/deleted, no global prune runs, and no host-network fallback exists.
Container endpoints belong to the existing exact-ID lifecycle owner. A failure
after create preserves its candidate native ID through the existing intent
carrier and leaves the Host charge/recovery obligation pending. It does not
report absence, release reservations, or retry an ambiguous create. Existing
strict recovery does not substitute for cleanup. A separate stop/destroy-only
path requires the provider's retained create-attempt/birth record, exact bound
request digest/operation and candidate ID, plus fresh engine, native-ID and
managed-scope ownership inspection. It ignores environment/endpoint readiness
so an immutable poisoned image environment cannot strand its created container.
Labels alone never establish birth. Only that exact owned ID may be removed,
and the existing positive-empty exact-ID absence query must pass before a
destroyed success. No start/admission path consumes this cleanup observation.
The private `native_birth_retained` record bit is set only by the actual expected
create completion owner with a captured valid native ID, including a completion
whose transport cleanup reports an error. Caller `RuntimeIntentV1` recovery
metadata never sets it. Recovered ready containers retain the existing strict
cleanup path (fresh network, complete inspection and effective environment);
poisoned recovered metadata cannot unlock relaxed cleanup. A stop may consume
its native effect then report blocked when its strict post-stop readiness
observation fails; the exact ID and charge stay pending. Destroy's successful
absence proof remains separate.

The portable Windows adapter's existing private `_owned(request,true)` and
retained native-ID check already prevent arbitrary intents entering its actual
service recovery path. Its authority array is populated by in-process create
completion, not caller data, and starts empty on a new service incarnation.
Protected Host archive packets in `host_execution_archive_v3` provide durable
plans/requests/intents/observations but are not themselves native birth grants.
To restore relaxed cleanup after restart, a future handoff must validate that
protected `DistributedOperationJournalV2` record, retained Host charge, exact
provider/service scope and completed create receipt/native ID, then mint opaque
birth custody into the canonical adapter/leaf. No caller boolean or copied
intent substitutes for that capability; this recovery-cleanup gap remains
explicitly unfinished rather than declaring permanent refusal a complete feature.

[Docker create](https://docs.docker.com/reference/cli/docker/container/create/)
documents environment, network and entrypoint options. Microsoft's
[Windows network driver reference](https://learn.microsoft.com/en-us/virtualization/windowscontainers/container-networking/network-drivers-topologies)
describes NAT/HNS and notes NAT networks may not persist across reboot. Exact
network IDs therefore require fresh deployment policy/observation after such a
change; names are never a fallback. Selecting NAT does not guarantee DNS,
routing, server authentication, firewall reachability or egress filtering.
The filtered inspection uses documented Docker [Go-template functions](https://docs.docker.com/engine/cli/formatting/)
`lower`, `split`, and `json`; no caller-supplied template is executed.

Qualification must provision the actual Windows host/image pair, exact NAT
network and non-loopback public server endpoint, inspect the actual create and
attached endpoint, run the container's Simple/Orchestrator/Caret discovery and
connection path, and exercise stale/removed/extra network failures. The current
host has no authorized native campaign; those observations remain NOT_RUN.
