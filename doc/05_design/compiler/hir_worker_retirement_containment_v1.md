# Selected worker retirement design: parent-trackable tools

Selected by user delegation and root: admitted parent-trackable tools.
Baseline309249bd1a0; design under Astra manager review. No production rollout
or native execution is authorized by this document alone.

## Shared contract before implementation

Keep canonical `ProcessObservationLeaseV4` and its request/pin/collect/ack APIs.
Every process is started by the surviving parent coordinator, including nested
compiler tools. The cancelled worker is not the sole owner of any child lease.

Proposed pure-Simple types (names reserved for this lane):
- `WorkerToolProfileV1`: profile_id, executable_digest, configuration_digest,
  spawn_contract, qualification_identity. Admitted spawn contracts are
  `broker_only_v1` for compiler workers and `group_preserving_v1` for externally
  qualified tools. Unknown profiles, expired/mismatched qualifications or mere
  executable names/self-declaration are not authority.
- `WorkerLaunchRequestV1`: request_id, parent_request_id, worker_owner,
  owner_generation, profile identity, exact argv/environment/cwd, absolute work
  deadline, bounded output and process budget. Immutable child-to-parent message.
- `WorkerLaunchOwnerV1`: parent-local executable/cwd pins, V4 lease, exact
  request identity, original work result, terminal/cleanup receipt, acknowledged
  state. No lease/PID capability crosses IPC.
- `WorkerOwnerEventV1`: immutable status/reason/request identity and bounded
  output; distinguishes work failure, retirement pending, retirement success,
  cleanup failure and protocol refusal.

New coordinator adapter functions: `worker_owner_start_v1`,
`worker_owner_tick_v1`, `worker_owner_cancel_v1`; owner methods delegate the
existing V4 lifecycle. The broker keeps pending/live owner arrays bounded by
explicit worker+nested capacity, validates parent-child owner/generation links,
and drains all leases fairly. Unknown child requests fail closed. Original
work timeout remains failure after successful retirement.

Admission is the essential guarantee, not a free-text flag: executable and
configuration hashes must match a qualified profile for the exact caller mode.
A compiler profile is not admitted until its actual reachable spawn paths use
the broker, including `native_codegen_pool_v1` and configured external compiler
execution. A group-preserving external tool can fork within its group but must
not daemonize, change group/session or use an untracked process service. Those
behaviors are outside this selected policy and cannot receive all_stopped.

## Transport and ownership

No existing release worker broker transport was found. Saved PR LSP artifact
code is not landed and must not be copied silently as a qualified owner.
Define one bounded private SDN request/result channel per worker, independently
owned by the parent, with exact nonce/owner/generation/request identities,
exclusive publication, bounded queue/bytes and retained cleanup-error ownership.
Use an existing canonical filesystem/IPC owner when selected; do not parse
arbitrary stdout as control and do not add app-local runtime externs.

The transport choice and concrete profile qualification authority require the
manager's pre-code review. A file spool must use bounded known leaves rather
than repeated unrestricted directory scans; a pipe needs a canonical owned
nonblocking duplex endpoint. Neither capability is assumed implemented merely
because this contract exists.

## Integration boundaries

Owned new files: `src/app/cli/worker_tool_policy_v1.spl`,
`worker_launch_owner_v1.spl`, `worker_broker_v1.spl`,
`worker_broker_protocol_v1.spl`; new `worker_*` focused tests/manuals.
Existing integration: `src/app/cli/native_build_main.spl`,
`src/compiler/80.driver/driver_build/native_codegen_pool_v1.spl`, plus the
canonical process facade only after exact overlap/interface agreement.

Other sessions own dirty runtime_process_owned.c, private cwd/SHA headers,
Darwin observation fixture, Rust runtime build.rs, bootstrap_builder specs and
runtime source-list baseline. This lane must not edit, incorporate or rerun them.
Astra manager owns independent final review; root owns native job slots and
integration/landing. No child agents delegated by this lane.

## Deadline and commit barrier

Use one absolute cleanup deadline <=5000ms for the entire worker subtree, not
5000ms per process. Cancel all admitted owners first, then poll/drain fairly.
All tracked leases must freeze exact terminal/tree-empty/reaped receipts,
acknowledge and close pins before all_stopped is true. Any unknown owner,
malformed identity, failed close/ack or deadline prevents replacement, ledger
closure, fallback and artifact publication. No post-reap raw PID signalling.

## Required tests and truthful completion

Names begin `worker_`. Actual accepted group-preserving tool and broker-only
worker controls; rejected/untracked/stale profile before launch; real nested
codegen child survives worker crash until parent retires it; TERM-ignoring
child; retained writer after leader exit; malformed request/wrong ticket;
cleanup/ack failure; fixed deadline/no per-child reset; exact argv/env/cwd/tool
identity and compiler outputs preserved. A deliberate escaping helper is
rejected by profile admission and must not be presented as a contained process.

Policy unit tests are not process proof. New native/provider and actual
coordinator tests must run under root-admitted slots. Existing40-assertion
session-owner PASS is historical and must not be rerun unchanged. No release
or full worker completion until real integration evidence passes and Astra
reviews the exact committed source. Retry limit: three additional meaningful
cycles, retaining previous lane history; deadline18:56:40UTC.

## Concrete wire proposal for pre-code review

Use `file_ops.secure_temp_dir` for the parent-owned0700 root;
`file_atomic_write` to a known staging leaf plus `file_publish_noreplace` for
publication; `file_read_regular_no_follow_bounded` for reads. Do not reuse
process_set's shell-listed/unescaped line transport. Trusted same-UID local
processes are assumed; this is not a hostile filesystem sandbox.

Parent writes `manifest.sdn` with schema `worker-broker-v1`, per-worker nonce,
worker_owner, owner_generation, worker_request_id, exact admitted profile digest,
and allocated slot count. Worker receives the locator only through the exact
parent-owned launch environment. Parent retains the corresponding manifest
value; file content is never its sole authority.

Allocated slots are fixed known integers. Each has `req.<slot>.sdn`,
`res.<slot>.sdn`, and `ack.<slot>.sdn`, with fixed staging leaves. No directory
scan. Request fields: schema, nonce, owner, generation, request sequence,
parent request id, tool profile id/qualification/configuration digest, pinned
executable digest claim, argv, environment, cwd, remaining work deadline and
capture limits. Parent matches request to its live root owner and compares the
claim to its actual executable pin before launching. A request cannot install
its own admission profile or enlarge its capacity.

Response fields: schema, exact owner/generation/slot/sequence, work status/code,
retirement status/reason, bounded stdout/stderr and result digest. Only a
parent-owned canonical terminal/ack result can produce retired success. The
client acknowledgment binds result digest and sequence; it releases the IPC
slot, not the native process authority (already retained/acknowledged by parent).
A dead worker need not acknowledge an unused result for its parent to retire
all native owners; it does not turn an uncertain native owner into success.

Initial proposed hard ceilings:128 total live owners,32 nested slots per worker
within that total,1MiB encoded request,4MiB encoded result,64KiB total environment,
256 argv entries,4096 bytes per locator/identity,25ms maximum poll wait. Native
process output budgets and SDN encoded-byte budget are admitted before material-
ization. Exact limits are implementation bounds subject to manager review, not
permission to silently truncate valid configured input. Oversize rejects before
launch with a named bound. Cancellation shares the existing5000ms overall budget.

Known active integration points: `native_build_main.run_ledger_shards` owns
spawn/poll/replacement/inventory state; its HIR, MIR and file-worker callers
require separate mode profiles. `native_codegen_pool_v1.native_codegen_child_spawn_v1`
currently calls raw session creation and must delegate to the broker for an
admitted compiler-worker profile. Synchronous configured compiler calls through
`process_run` also need owner routing; catching only the codegen session call
is insufficient. The inventory agent is proving the HIR-only reachable set
before a production profile is admitted. No unconditional compiled-tool profile
exists yet in this draft, and that absence is an open completion obligation.

## Narrowed first profile under proof: compiled HIR frozen closure

This is an initial admitted-profile candidate, not completion of generic broker
or MIR/file-worker containment. Admission must occur in the parent before V4
launch, and before child loading can act on environment injection.

- Exact producer: retained launch pin digest must match a qualification record
  for the compiled internal worker dispatch. `run ...native_build_worker.spl`
  is admissible only when the qualified producer dispatches it through
  `bootstrap_internal_worker_routing`; an older source-interpreting fallback is
  a different, unqualified profile. Linked runtime/system-library assumptions
  are explicitly part of the qualification identity.
- Mode: exactly one validated HIR shard index/count and a parent-installed
  frozen closure request. No file-worker unit, MIR/parse shard combination,
  native-group mode, source-epoch mix, plugin override or delegated compiler.
  A request cannot remove these exclusions by supplying its own config digest.
- Source authority: parent retains the admitted NativeEntryClosureRequestV1 and
  approved policy digest. Worker uses the existing request read/open path and
  `effective_entry_closure`, so input_files are the selected snapshot files.
  Missing/changed membership or an import outside that authority must fail,
  never fall back to directory discovery or host-source search.
- Environment/config: reject loader-injection variables (including LD_*/DYLD_*
  family) and unqualified compiler/tool/plugin route overrides. Validate the
  complete captured argv/env/cwd against the parent's admitted configuration;
  derive configuration_digest only after validation. Preserve configured values
  or reject explicitly; do not silently sanitize into a different build.
  Tool search paths and external configuration files are admitted dependencies,
  not authority established merely by hashing an arbitrary request string.
- Deadline: parent computes `min(parent_absolute_deadline,
  admitted_request_deadline)` once; an IPC request, retry or polling iteration
  cannot restart the remaining budget. Cancellation uses one separate fixed
  overall cleanup deadline <=5000ms for every outstanding admitted owner.

Concrete source evidence at309249: compile_targets1540–1589 admits/opens the
parent closure;1615+ uses its explicit file identities. The HIR lowering owner
actually exits after ledger completion at2417–2427 (non-streaming) and1521–1532
(streaming unless file-worker-unit). The closure owner's plain-checkout helper
is pure path routing; receipt admission reads/hashes snapshot and inventory.
TLDR git notes/log helpers have CLI tldr callers only in the bounded call search,
so their mere presence in a cache source file is not a HIR reachable-spawn proof.

Bounded startup audit closes the remaining named source boundary at this frozen
revision: native_collection_profile calls compiler_driver_run_compile; driver
construction installs backend function closures without invoking them;
driver_orchestration loads the take-once closure handoff, parses and lowers HIR
before later backend dispatch. Managed runtime preselection calls canonical
runtime/tool snapshot owners that read/hash/stat pinned files; resolving the cc
role does not execute cc. The TLDR freshness operation is also a file/hash
operation; git helpers belong to separate CLI commands. HIR error handlers
publish diagnostics and terminate without invoking later code generation.

The directory shell-find owner at driver_source_pipeline_loading200 is excluded
only while actual driver_inputs remains nonempty: its call at814–837 requires
input_len<=0. Empty package-index archives fail explicitly. Admission must reject
all routing that can replace the selected nonempty closure with empty inputs.
Bounded inspection of parser preprocessor, AOP, HIR lowering and ICE handling
found no further executable process calls. This is bounded source evidence,
not runtime qualification or an arbitrary dynamic-code containment guarantee.
Actual consumer execution and exact configuration admission remain required.

## Initial profile integration contract (pre-code review)

Production ownership is limited to new app CLI worker_hir_profile_v1 and
worker_hir_owner_v1 modules, HIR-only routing in native_build_main's shared ledger
coordinator, and profile validation at native_build_worker_entry. MIR/file pools
and native_codegen_pool remain outside this initial migration. The profile owner
retains approved configuration and canonical closure authority; the process owner
retains executable/cwd pins and V4 lease until terminal certification and frozen
acknowledgement. Cleanup failure retains owner identity and blocks ledger sealing,
inventory close, fallback and success. Timeout remains failure even after cleanup.

Tests must exercise the actual internal worker entry on a small explicit closure
and inspect the resulting HIR artifact; rejection controls cover empty inputs,
mixed modes and environment injection before launch; owner controls cover timeout,
acknowledgement and cleanup failure. Unit policy tests alone cannot qualify this
profile. Proposed specs are worker_hir_profile_v1_spec.spl under unit app/cli and
worker_hir_retirement_v1_spec.spl under integration/app. Generic parent-brokered
tools remain selected requirements and are not marked complete by this profile.

## Authored first profile, 2026-11-07

The four app owners are now implemented against a1e831a2b569775db2193d53f686ea87cc5a2d23.
The real ledger HIR path admits the execution argv after its exact internal
`run src/app/cli/native_build_worker.spl` prefix. This preserves the focused
capsule's canonical attached policy handoff even when its separate public args
omit that internal field. The decoded handoff policy digest, not the closure's
own policy claim, is passed to closure open. Native startup derives launch
identity from the retained executable pin and compares it with the closure
producer. The worker validates the existing closure receipt again before compile.

`WorkerHirProfileV1` owns argv, the full admitted environment, canonical closure,
configuration digest and absolute pool deadline. Admission rejects unknown
option/environment keys; its literal lists are versioned in
worker_hir_profile_v1.spl. It supports compiled internal HIR dispatch only,
not interpreted wrappers. The 128-owner pool ceiling and one-hour default
absolute work ceiling are explicit initial-profile policy. Configurations outside
this first profile are rejected, not silently rewritten into a different build.
Canonical managed-authority fields are admitted as data; arbitrary CC/linker or
loader-injection overrides are not.

`WorkerHirOwnerV1` owns executable/cwd pins and V4 lease, including partial start
and failed cleanup. tick collects the exact ticket, requires leader-reaped and
tree-empty, acknowledges the frozen receipt and then closes pins. Cancellation
keeps a failed work code. The coordinator starts sibling cancellation before
waiting and never seals an unretired owner. A failed owner is retained and prevents
future starts in that process. One fixed cleanup interval is at most5000ms;
polling never resets it. App code never signals a raw PID for this HIR path.

Concrete unresolved canonical dependency: process_observation_owner_start_pinned_v4
may decode-fail after native start without returning a lease. Existing scheduler
transport code already records this production blocker. The new HIR adapter
retains its available pins, marks launch_uncertain/all_stopped=false and blocks
success; it does not claim that those pins can stop the missing process owner.
An owner-boundary repair is required to qualify full cleanup under this fault.

Specs/manual are authored, NOT_RUN. Real internal-dispatch/HIR artifact,
cancellation, deadline and controlled invalid-ticket tests exist; coordinator
replacement/sibling execution and native signal/close fault qualification remain
open. No supported-platform, latency, RSS or full generic-tool completion claim
is made by this source-only implementation.


## E3 reservation integration (current source)

Canonical dependency a4610ebbbbb3bde8e8aff8ff85a5ba57da5b7f25 supplies
ProcessObservationReservationV4. The app now reserves authority before invoking
start, retains that reservation on every Result error, and retires via observe.
READY/NO_CHILD can confirm release without a fabricated process receipt.
OWNED/ACKED return the original frozen observation: acknowledge(binding) is
repeatable, and confirm_release requires the decoded acknowledgement before pins
close. The earlier legacy-facade start/ack-loss finding is addressed for this
consumer by this explicit dependency; other legacy callers are not certified.

The fixed shared deadline, fair sibling drain and failed-outcome preservation
remain unchanged. Successful native focused C controls belong to the canonical
owner's evidence. The app/Simple facade and integration specs are still NOT_RUN.
The decoder-persistence control starts a real reservation, projects its real
observation losslessly into the published wire layout, proves positive decode,
corrupts the version and requires decoder rejection, then retires/acknowledges/
confirms that same owner. This is composition coverage, not injection within
observe. It also requires early release refusal, malformed-ack refusal and
repeatable valid acknowledgement before successful release and pin closure.
