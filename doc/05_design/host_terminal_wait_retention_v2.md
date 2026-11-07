# Full runtime observation transport and original terminal-wait retention V2

Status: **SOURCE_IMPLEMENTED / NOT_RUN**. No compiler campaign, admitted runtime
suite, native engine or live-platform qualification was performed. This change
is reviewed together with retained execution resolver dependency `a3826478ed7`
(cherry-picked as `d1e7f919d5f`) and Linux readonly descriptor-sync dependency
`10408c1baea` (cherry-picked as `2c7a7e1089d`) in the isolated terminal-wait branch.

The shared runtime-operation codec transports the complete `RuntimeOperationV1`:
status, operation, exact command/program/argv, full state/runtime identity,
separate CLI and workload exit codes, stdout, stderr and both reason fields.
Canonical SDN uses exact known/type/missing-field checks, a 2 MiB byte bound,
4,096 argument bound, maximum depth four and bounded parser nodes/columns.
Rejected/empty observations remain representable as data; decoding does not
turn them into terminal authority. The existing
`container_runtime_observation_digest_v2` is used unchanged.

The pure common `host_terminal_wait_receipt_v2` module owns the receipt type,
canonical codec and one qualification function shared by host collection and
cleanup projection. It imports no HostLocalRoot, filesystem, provider or capacity
owner. Its 8 MiB document cap accommodates escaped full 2 MiB runtime wire plus
the execution plan and correlation metadata. Qualification checks exact plan,
operation/provider digests, all runtime identity fields, full 64-hex native ID,
backend/engine consistency and scope fence. Only a successful actual wait command
with CLI exit zero, exited/stopped phase and nonnegative workload exit qualifies.
Workload exit 17 remains 17; it is neither inferred success nor a native signal.

`host_terminal_wait_v2` keeps the existing held host-journal writer and returns
the complete updated `HostLocalRootV1` on every post-native failure. The only
caller-supplied lookup is the operation ID. An existing original receipt is
loaded and correlated through `host_local_retained_execution_v2` before any
native resolver/query. If absent, the shared execution resolver supplies the
protected exact request and current common owner; common `read("wait")` then
performs the native wait. The host reads its actual Unix clock after that wait.

Before the actual wait, the same owner exclusively creates and synchronizes an
immutable collection claim bound to the exact execution/op/provider/native ID.
The claim is a canonical SDN dictionary with version/kind, plan digest,
operation digest, provider digest and full native ID; loading compares exact
expected bytes and introduces no second parser.
If a crash leaves that claim without a valid complete stage, collection reports
recovery-required and never re-waits or invents a fresh original timestamp.
A qualified in-process observation survives publication failure as
`Some(receipt)` plus a nonempty error; it is pending data, not durable success.
The gap before any complete receipt bytes persist is deliberately unresolved.

The immutable final fact lives at
`<existing-host-journal>/host-terminal-waits-v2/<sha256(operation_id)>.sdn`.
This is a retained fact under the same owner, not another journal/provider/WAL.
An exact private writable owner creates `.write`, completes bounded writes and
fsyncs that descriptor. Readback checks actual descriptor ownership/mode and
unchanged identity. No-replace publication first creates complete `.stage.sdn`,
then the final receipt; directory metadata is synchronized before delivery.
A failed read or store retains the actual updated owner and capacity charge.
Existing corrupt/unreadable/permissive facts fail closed. If an
ambiguous existence check misses a hidden/dangling object, exclusive publication
still prevents replacement or a freshly stamped successful result. No second
pending journal or overwrite is introduced.

Repeat/reopen preserves original bytes and timestamp, including when the provider
object is unavailable or already destroyed. A valid complete stage resumes
publication with those same bytes/time. Retained replay revalidates the exact
read descriptor's effective-UID ownership, mode 0600 and unchanged identity;
it never chmods an existing file. It synchronizes the exact readonly Linux
descriptor through the separately admitted retained-owner capability, verifies
identity again before close, and retries directory metadata synchronization.
Original stage data was already fsynced under its writable owner. Replay performs no native query and does not renew
execution authority. The collector neither releases capacity nor grants launch,
destruction, absence, cleanup or task success. Native cleanup remains a separate
freshly authorized owner operation that can consume the pure qualified fact.

Private persistence currently fails explicitly outside Linux. The existing
Linux retained-directory/file owner inspects actual descriptor metadata;
Windows chmod/stat are not an ACL proof and no Windows private-owner admission
is claimed until its native capability is integrated. Trusted-directory ancestry
rules remain unchanged, including supported root-owned sticky temporary parents.

Source specifications include five codec cases, four pure receipt cases and nine
real common-API/journal/filesystem retention cases. Native engine commands and
host metadata in those fixtures are explicitly scripted; the signed executor,
shared owner, leases, journal reopen and file retention are actual APIs when run.
The destroyed/unavailable fixture is explicit state data, not a destroy command
or an absence receipt. No fake live-platform or coverage PASS is inferred.

No full-tree scans, provider discovery loops, retry sleeps or direct native engine
subprocesses are added. The wait uses the existing common API. Fresh collection uses the resolver's returned execution and
observation directly; repeat collection uses the shared pure retained resolver
once. All documents/parser work are bounded. Runtime latency/RSS measurements,
durability behavior and platform qualification remain unverified.
