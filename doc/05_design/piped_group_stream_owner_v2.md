# Group-broker-backed live pipe ownership V2

Status: DESIGN / AWAITING_VERIFICATION. Base
862d9e361534c1a13f83a2f43da06e07847df5af; isolated branch
work/piped-group-owner-20261107. Root selected the existing durable group broker,
not the separate native V3 captured-process registry. Implementation is now
written in the isolated source tree; new bounded native syntax checks are
recorded separately. No runtime/SPipe qualification is implied. Native ABI was
reviewed by Astra; pinned-root and exact-start refinements below are mandatory.

## Frozen public interfaces

Common module `group_process_stream_protocol_v2` defines:

- GroupProcessStreamRequestV2: program, producer_digest, args:[text],
  environment:[text], directory, inputs:[GroupProcessInputV1], timeout_ms:i64,
  broker_program, broker_digest, child_argv_digest, launch_deadline_unix_ms:i64.
- GroupProcessStreamLaunchV2: root, worker_id, generation:i64, snapshot_digest,
  cache_identity, memory_limit_bytes:i64, request, delegated_cgroup_path,
  memory_policy:text="enforce", transport_generation:i64=0.
- group_process_child_argv_digest_v2(program,args); canonical strict launch
  validation/encode/decode with header SIMPLE-GROUP-STREAM-2.
- GroupProcessStreamOwnerV2 contains the full launch and its identity digest.
- PipedProcessOwnedTransferV2 contains owner and reference; a bare Ref is not the
  complete service ownership transfer. PipedProcessOwnedSpawnV2 is Ready(owner,
  reference), CleanupRequired(owner,reference?,reason), or Rejected(reason).
- process_spawn_piped_owned_v2(launch), process_cleanup_piped_owned_v2(owner,ref?),
  group_process_stream_collect_reap_v2(owner,GroupedActionLeaseV1) returning the
  existing GroupedReapReceiptV1 for host ledger release.
- PipedProcessRefV1 adds default-empty group_root/group_identity. Equality helper
  process_piped_ref_equal_v1 and SOSIX alias compare all four fields. Existing
  stream/lifecycle method names remain. Unowned POSIX lifecycle stays unsupported.
- process_validate_piped_owned_transfer_v2 validates canonical full owner and
  root/identity/transport generation against native binding without reading,
  liveness or broker control. process_piped_owned_transfer_equal_v2 compares full
  canonical owner provenance and all Ref fields; invalid owners never match.
  Both have SOSIX aliases; no extra resource ledger is added.

## Admission, ownership and state transitions

Caller launch transport_generation must be zero. Validate canonical bytes,
portable absolute/NUL-free path shapes, child argv digest and budgets; Linux
then requires actual nonempty delegated cgroup admission before
helper fork. A real native capability/delegation admission must succeed; platform
names, file existence or caller booleans are insufficient. Unsupported hosts fail
closed. Reserve a stream ticket in the existing pipe registry first, insert its
actual generation into a prepared launch, encode/hash, then bind immutable
root/identity to that ticket. Persist claim and request before launching broker.
Claims and terminal/audit artifacts are never erased as a cleanup shortcut.

Ticket states: reserved -> bound/prepared -> launching -> broker-published ->
terminal-proven -> retired. Failure before any fork may reject only after native
unlaunched-ticket abandonment succeeds. Once launch may have happened, return
CleanupRequired with full owner and optional reference. A launch receipt can
publish broker PID into the already reserved slot; it never adopts by PID lookup.
If no PID receipt exists, owner.launch.transport_generation still locates the
exact pending ticket for cleanup. No exception discards launch provenance.

The pipe slot owns byte endpoints and generation/binding. The existing independent
broker is the sole workload lifecycle supervisor. Caret remains sole pane reader;
no broker/owned-V3 capture routine reads the child's stream. All read/write/state/
validate operations check PID+generation+root+identity during the actual native
operation. Old native Ref/PID operations refuse bound slots; legacy unbound
behavior remains unchanged. Root/identity are local binding metadata, not remote
authority and not a substitute for retaining the full owner request.

Common encoding is engine/platform-neutral: POSIX, Windows drive-absolute and
UNC spellings are shapes, not host admission. Generic delegated_cgroup_path may
be empty. Linux native admission separately requires a real delegated cgroup;
this does not admit Windows owned streams or change legacy Windows Ref support.

## Admission deadline (launch only)

A required positive launch_deadline_unix_ms is canonical request-bound. The
trusted host supplies the minimum verified grant expiry; accepting a remote
request's value alone is not authorization. Broker checks a real Unix-ms clock
immediately before actual helper launch; the native child rechecks immediately
before execveat, preventing slow admission from crossing expiry. No fake/caller
clock or success boolean enters production. Expired admission fails before new
helper effects. Expiry is admission only: request.timeout_ms remains the separate
signed workload lifetime (zero allowed by policy). Never cap duration or kill a
running session because grant/heartbeat expires. Recovery and durable ownership
continue after admission expiry; expiry is not capacity-release proof.

## Descriptor and broker composition

Refactor the existing detached pinned Linux broker launcher, retaining image
verification and execveat. The launcher borrows independently duplicated endpoints
from the reserved ticket under a launch claim. Native-private borrowed descriptors
are an explicit owned move scoped to launch; no raw FD crosses the Simple ABI.
Normalize source descriptors above5 before remapping to avoid dup2 alias hazards.
Broker stdio0/1/2 remains /dev/null. Its only explicit extra inherited FDs are
4 child-stdin-read and5 child-stdout/stderr-write. Pinned image FD3 remains CLOEXEC;
4/5 survive broker exec. All other descriptors close. Errors retain pending owner
and close only the launcher's own duplicate descriptors.

Broker main dispatches V1 or strict stream V2 from the immutable request header.
The stream profile uses the same admission/control/cgroup cancel/poll/collect
state machine. Native stream start reuses the existing cgroup clone3+pidfd owner,
validates inherited descriptor kinds/directions, duplicates4->child0 and5->child1
and2, then closes extras before executing pinned worker image3. The broker does
not redirect its diagnostics into5. It owns no alternate stdout reader.

## Lifecycle and retirement

Bound Ref lifecycle delegates to the existing broker challenge/terminal protocol
through Simple policy. EOF and group exit remain distinct. Cancellation follows
existing cgroup.kill and populated=false plus leader reaped proof; no PID/PGID
fallback or second supervisor is added. Cleanup errors retain owner/ticket and
permit bounded explicit cleanup retries, never replay launch.

Native descriptor retirement requires the same bound generation/root/identity
and exact persisted terminal proof. Proposed division: Simple validates the
existing canonical terminal observation and identity; native retirement rereads
the protected terminal file no-follow/bounded and compares exact supplied proof
bytes before closing the bound descriptors. This is not a caller boolean. Lead
must confirm this minimal byte-equality barrier is adequate before implementation;
do not duplicate broker policy parsing in C. A missing/changed proof retains
endpoints. Collect-reap then binds retained terminal evidence to the existing
GroupedActionLeaseV1; descriptor retirement does not delete audit artifacts.

Recovery may reconnect to/cancel the existing broker and collect durable proof,
but cannot recreate the vanished host's byte endpoints or launch another worker.
Host loss is cleanup-only. Stale generations, bindings and duplicate close have
no effects. Resource accounting and locking remain explicit and bounded.

## Reviewed native ABI and mandatory refinements

Names below are additions; existing public Simple APIs remain frozen. All scalar
status APIs use0 success, negative explicit error, preserving owner on uncertainty.
Text uses explicit counted bytes at the boundary. New binding-aware action names
avoid changing the already published unbound native ABI.

| Native operation | Proposed signature / responsibility |
|---|---|
| reserve ticket | rt_process_stream_reserve_v2()->i64 exact positive generation, pipes in existing registry |
| bind prepared owner | rt_process_stream_bind_v2(generation,root,root_len,identity,identity_len)->i64; one-time binding |
| abandon before fork | rt_process_stream_abandon_unlaunched_v2(generation,root,root_len,identity,identity_len)->i64; refuses after launch claim |
| launch pinned broker | rt_linux_group_launch_stream_broker_v2(program,program_len,digest,digest_len,args,generation,root,root_len,identity,identity_len)->[i64] PID/error receipt using existing launcher ownership |
| bound read/state/validate/write | rt_process_{read_stdout,stdout_state,validate_piped,write_stdin_some}_owned_v2 with pid,generation,root/root_len,identity/identity_len plus existing write byte/range args; same reader/registry |
| retire descriptors | rt_process_stream_retire_v2(generation,root,root_len,identity,identity_len,terminal_bytes,terminal_len)->i64; no lifecycle signalling |
| inherited-stream group start | rt_linux_group_start_stream_v2: existing admitted group start inputs minus output paths, fixed4/5 endpoints, same cgroup/pidfd owner |

Native-private handoff helper returns duplicated launch endpoints only to the
pinned launcher, guarded by a slot launch claim. No language pointer/FD/out-param
ABI is introduced. Existing group poll/cancel/collect APIs and receipt remain.

## Exact implementation file plan

Pure Simple: new common protocol; io/group_process_owner.spl refactored reusable
prepare/confirm/control and V2 owner; io/process_ops.spl plus SOSIX aliases;
io/linux_process_owner.spl; bootstrap_builder/native_group_linux_launcher.spl
and native_group_linux_broker.spl stream dispatch. Existing V1 validation and
wire restrictions remain unchanged. New shared helpers must retain all V1 cases.

Native boundary: runtime_process.c/runtime.h canonical tickets/binding/reader and
runtime_linux_group_owner_impl.h existing pinned launcher/cgroup descriptor mode.
No native V3 supervisor or compiler changes. Existing native admission source
wiring is reused. Any additional required provider declaration is reviewed first.

Tests/manuals: strict common protocol spec; pipe/broker owner failure-stage spec;
actual native boundary fixture for inherited FD allowlist, diagnostics isolation,
stale binding/no effects, EOF-before-tree-exit, descendant retirement, delegation
failure and host-loss cleanup-only. Each fixture has finite resources/deadline and
private output. No old green native harness is rerun. CPU affinity0-4; no native
build until exact source/scope notification and lead/root allocation.

### Reviewed native safeguards

Binding pins the protected root with O_DIRECTORY/O_NOFOLLOW and validates local
ownership, permissions and identity. Retirement uses openat on that retained
directory FD, never reopens a mutable root pathname as authority. It compares
bounded regular terminal bytes that the existing Simple canonical validator
accepted; native code adds no second policy parser.

After confirmed one-time broker inheritance, the host closes only its own
child-facing duplicates. Host read/write endpoints remain until terminal proof.
Broker closes inherited4/5 immediately after successful child handoff; holding
those copies would incorrectly defer workload EOF. Diagnostics remain /dev/null.
Unknown handoff retains owner and ticket without replay. An child-start
receipt distinguishes a reported exec/admission failure from a successful broker fork.
Deadline rejection before exec cannot become Ready. Existing error/lease receipt
machinery retains cleanup authority through every post-launch failure.

### Implemented additional native projection and unavailable leaves

linux_process_owner.spl exposes actual stream-start Ready/CleanupRequired/Rejected
outcomes plus Unknown for malformed native receipts. The broker retains authority
on Unknown. `rt_linux_group_collected_stream_v2(token)` projects the same actual
collected observation without any OS access, permitting recovery after destructive
collection followed by value-allocation failure. Stream publication retains that
receipt in Simple; it never recollects after persistence failure. Known no-clone
rejection publishes SIMPLE-GROUP-STREAM-UNLAUNCHED-2 only after actual parent
release and persisted capacity.released. Native retirement selects the corresponding
pinned-root file by the exact profile header; it does not invent tree flags.

New native Linux leaves are rt_linux_group_stream_admit_v2,
rt_linux_group_launch_stream_broker_v2, rt_linux_group_start_stream_v2,
rt_linux_group_collected_stream_v2 and rt_linux_group_stream_release_inherited_v2.
Explicit non-Linux/CORE_ONLY definitions return ENOTSUP/error receipts, preserving
cross-platform linkage without claiming another native provider. New ticket/action
leaf declarations live in runtime.h; native-private claim/publish/no-fork reset
helpers use C-only descriptor out parameters, never the language ABI.

## Source freeze and evidence status (2026-11-07)

Implementation is written, not fully qualified. A new normal-CoreC native fixture
built and ran successfully after correcting its raw-exit receipt index oracle.
Exact source/binary hashes, commands, logs and both outcomes are retained under
build/piped-group-stream-v2; the tracked asset
`doc/06_spec/01_unit/lib/io/piped_group_stream_transport_v2_evidence.sdn`
contains source hashes and exact commands for the precise pre-header snapshot.
This proves ticket/binding/reader transport behavior only: actual moved endpoints,
raw-adapter denial, one-shot claim versus known no-fork reset, stale generation
reuse, and pinned-directory refusal of a forged proof in a replacement path.
It does not prove actual cgroup admission, broker workload startup, descendant
retirement, Windows owned streams, or admitted Simple/SPipe execution. Existing
old green harnesses were not rerun. Header-only declarations added after that
snapshot are explicitly not represented as compiled evidence for those lines.

Ready means an owned transfer is available, not successful workload exec, protocol
readiness or attachment. EOF on the CLOEXEC error pipe reports no recorded error;
an externally killed pre-exec child can also close it. Positive exec/attach proof
requires the consumer's real protocol readiness checks. A terminal-before-transfer
owner maps to CleanupRequired, never fabricated successful attachment. Native
pre-exec deadline rejection that reports its error retains a cleanup lease.

The broker uses typed parent admission directly. CleanupPending retains its real
parent across release failures; Rejected is a native no-parent/no-child fact and
can publish a distinct unlaunched admission proof after dropping inherited stream
endpoints, without inventing a released-parent receipt. Unknown retains the broker
and native authority; it cannot claim terminal cleanup or replay startup. Child
start reserves its result storage before effects and supports exact scalar native
lease recovery, so allocation failure cannot erase an established child lease.
Actual collected observations are retained in Simple through failed publication;
final memory evidence uses the collected observation's own peak. Required full
broker/delegation/fault/expiry/descendant tests remain pending rather than passing
by absence of a configured provider.
