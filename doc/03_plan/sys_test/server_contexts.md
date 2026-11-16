# Server contexts verification plan

Status: **NOT_RUN / AWAITING_VERIFICATION**. No admitted self-hosted runtime is
available in this session. Source review and authored assertions do not satisfy
the execution gates below. This plan does not mark the broader orchestration
feature complete.

Authorities: [selected requirements](../../02_requirements/feature/server_contexts.md),
[NFRs](../../02_requirements/nfr/server_contexts.md),
[architecture](../../04_architecture/server_contexts.md),
[design](../../05_design/server_contexts.md), and
[setup guide](../../07_guide/tooling/orchestration_server_contexts.md).

| Gate | Mechanism and required evidence | Requirements | Current state |
|---|---|---|---|
| Pure schema/selection | Run `test/01_unit/lib/common/config_core/server_context_v1_spec.spl`; capture actual scenario and assertion results. Check precedence, unknown/duplicate fields, dangling references, negative endpoint forms, constructor validation, byte/count/depth limits and container address selection. | REQ-001, REQ-002, REQ-003, REQ-005; NFR-001, NFR-002 | 18 scenarios authored; NOT_RUN |
| Discovery and legacy local behavior | Exercise explicit config, default discovery, HOST CONFIG `server_config`, absent defaults, unreadable files and malformed selected files. Existing local commands must retain behavior; rejected explicit config must not fall back. | REQ-001, REQ-002, REQ-003 | Loader/CLI lane; NOT_RUN |
| SSH profile and argv | Run the transport owner's focused specs. Assert reference matching, private identity/known-hosts files, fixed compiled executable and command, strict host-key checking, disabled forwarding/config inheritance and no task-field interpolation. | REQ-002, REQ-003; NFR-002 | Specs authored in transport lane; NOT_RUN |
| Public identity and pinning | Run `host_identity_v1_spec.spl`; check canonical Ed25519 public wire fingerprints, independent first-pin comparison, changed-key refusal, public-only export, private codec fixtures and validation before store IO. Then separately exercise actual entropy, generation and OpenSSH interoperability. | REQ-002, REQ-007, REQ-009; NFR-002 | Pure/early-rejection assertions authored; provider effects NOT_RUN |
| Correlated identity exchange | Run `host_identity_exchange_v1_spec.spl`; preserve the full pending receipt through gateway normalization, bind it to the original upload, reject false grants/possession and mismatched action/controller/UID/server, and preserve nonzero transport replies. A deterministic callback is codec evidence only. | REQ-002, REQ-004, REQ-008; NFR-002, NFR-003 | Composed callback specs authored; real exchange NOT_RUN |
| Retained private store | Admit the `std.nogc_sync_mut.io.host_identity_store_v1` platform provider. Exercise private key/pin publication, reread/conflict handling, no replacement of changed pins, file and namespace sync distinctions, failure cleanup and retained owner propagation. Pending public registration must not install an authorization grant. | REQ-004, REQ-009; NFR-002, NFR-003 | Actual POSIX/Windows store effects NOT_RUN |
| Generic counted-stdin platform boundary | Run `test/01_unit/lib/io/stdin_command_contract_v1_spec.spl` for shared path/digest grammar. Separately admit `stdin_command_v1` POSIX/Windows selection, executable digest verification, counted input, explicit environment, finite polling and retained collection. Windows requires the real `windows_stdin_command_owner_v1` and protected-store ACL admission, not POSIX mode emulation. | REQ-002, REQ-003; NFR-002, NFR-003 | Pure contract cases authored; native providers NOT_RUN |
| Process lifecycle | Exercise bounded success, malformed/correlated reply rejection, excess output, timeout, cancellation and failed collection. Verify retained ownership whenever collection is unresolved; no automatic mutation retry. | REQ-004; NFR-003 | Transport lane; NOT_RUN |
| Installed gateway policy | Reject foreign controller ID, disallowed action, missing/unknown request fields and invalid action data. Verify trusted remote profile independently fixes root/controller/actions; client request cannot replace it. | REQ-003, REQ-004; NFR-002 | Gateway lane; NOT_RUN |
| Real controller journal | On isolated disposable state, submit a valid resource, inspect the same UID and cancel with its expected digest. Inspect journal/state receipts. Confirm intent/cancellation semantics without claiming observed execution/termination. | REQ-004 | System evidence absent; NOT_RUN |
| Signed execution ownership | Exercise dispatch/resume/inspect-execution using existing signed packet, controller and host owners; reject invalid signatures/identities and preserve cleanup ownership. | REQ-004 | System evidence absent; NOT_RUN |
| Real remote host | Install the compiled peer, trusted gateway config and independently verified identity. Resolve and send one read-only request before isolated mutation cases. Preserve exact request/reply correlation and unknown outcomes. | REQ-003, REQ-004, REQ-006 | No deployed peer/address supplied; NOT_RUN |
| Unsigned container preparation | Run the actual application preparation command for each backend; assert complete unsigned request and selected snapshot are included before digests, candidate scope/policy confer no authority, and the command performs no execution. The missing signing/reservation/submission composition is an implementation gap. | REQ-005 | Source preparation lane; NOT_RUN |
| Container clients | Through the existing Simple Container API, run LinuxPodman and WindowsDocker clients with an explicit reachable endpoint and separately approved scoped credential injection or host proxy. Never mount the host shared private keystore. Reject host loopback/local transport. Record actual DNS/connectivity and backend identity; expose no runtime socket. | REQ-005 | Both backends NOT_RUN |
| Performance | Measure warm compiled startup, representative request latency and peak RSS on realistic config/request fixtures, including both container backends. Capture bounded buffers, timeout and process collection. Do not substitute static limits for measurements. | NFR-001, NFR-003, NFR-004 | No measurements; NOT_RUN |
| Documentation/manual quality | Inspect guide, host identity guide, wiki crosslinks and exact spec/manual correspondence. Replace manually authored status only after actual SPipe docgen; require no placeholder assertions. | REQ-006 | Manual authored; runtime/docgen NOT_RUN |

Use the admitted pure-Simple self-hosted runtime. Do not bootstrap or substitute
the Rust seed to label this lane green. Record producer path/version/hash,
source revision, backend, linked runtime/provider, fixture identity and cache
scope with each executed gate. Acceptance criteria are verified once per
session; a changed implementation or new failure evidence is required for a
retry, within the repository's six-cycle limit.

Compiler/core/library integration additionally requires the repository's
compiler, library, MCP and LSP checks and core/MCP runtime smoke gates. Package
smokes apply if packaging changes. Run the working/staged direct-env runtime
guards and verify no executable `*_spec.spl` lives under `doc/06_spec` before
landing. The working/staged guards, shell syntax, staged whitespace and
zero executable-spec layout checks passed once for this candidate. Owned specs
contain no placeholder-pass matches. Two pre-existing host-config wiki links
remain broken; no newly added relative documentation link is broken. These
static results do not satisfy the runtime gates above.

The [unit manual](../../06_spec/01_unit/lib/common/config_core/server_context_v1_spec.md)
records the eighteen authored scenarios. The authored system SSpec is
`test/03_system/app/orchestrator/feature/server_contexts_spec.spl`; its manual
belongs in the matching `doc/06_spec/03_system/` subtree. It covers actual
controller entry points but remains NOT_RUN.

Additional manually authored, NOT_RUN companions:
[SSH profile/framing](../../06_spec/01_unit/app/orchestrator/server_ssh_v1_spec.md),
[public identity/private codec](../../06_spec/01_unit/app/orchestrator/host_identity_v1_spec.md),
[identity exchange](../../06_spec/01_unit/app/orchestrator/host_identity_exchange_v1_spec.md),
[controller gateway](../../06_spec/01_unit/app/orchestrator/controller_gateway_v1_spec.md),
and [counted-stdin admission](../../06_spec/01_unit/lib/io/stdin_command_contract_v1_spec.md).
The store and Windows command owners are dependencies, not qualification
inferred from these pure manuals. No docgen, native/provider execution,
filesystem durability, enrollment, grant or container success is asserted.
