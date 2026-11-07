# Opt-in remote BuildRunner completion

RUN-01 / RUN-02 source status: **AWAITING_VERIFICATION**. Do not enable the legacy
remote database path by removing its guard. No compiler or seed retry was run.

1. Prepare a BuildTask with immutable action, producer/toolchain/input/output
   identities and a pinned `RemoteEvidencePolicyV1`. Test policies require exact
   case IDs and a declared report output. Pin the canonical TraceRunPlan as
   `remote-tests/<task-id>.sdn` when using the event reporter bridge.
2. The protected controller prepares `RemoteAuthorityContextV1` from its original
   signed grant and approval, enrollment keys, observed environment, current
   policy/revocation/session, time and active assignment/epoch. Never populate
   these trusted fields from a completion response.
3. For native-domain execution, the enrolled host calls `remote_host_start_v1`
   with its local BuildHost and existing process port. `collect` requires real
   terminal/tree closure, rehashes inputs and captures actual binary outputs,
   logs and compiler process evidence before producing a signed bundle.
4. Encode/decode via `remote_bundle_encode_v1` / `remote_bundle_decode_v1`.
   The transport is bounded and canonical; a decoded bundle remains untrusted.
5. Open the explicit `remote_database_session_open_v1` adapter around the
   existing task journal and owned operation journal. The operation must already
   be durably executing. Call `accept_wire` with fresh protected authority.
   Only its successful return exposes the accepted result and parent output root.
6. Route cancellation through `RemoteDatabaseSessionV1.cancel`. It rejects a
   foreign operation and refuses cancellation after the task result commit,
   requiring exact-evidence reconciliation. Ask the host execution owner to
   cancel/reap separately; durable cancellation alone is not cleanup proof.

The task database append uses operation ID as its stable group. The subsequent
operation terminal commit can be recovered after reopen from the exact retained
result/process digest. Do not directly cancel the injected operation journal
behind the remote adapter. Do not publish the quarantined output root into a
cache when `accept` returns an error. Existing database settlement/release and
operation-journal release remain owned by the outer run supervisor.

The dedicated `remote_test_runner_v1` producer calls the existing native test
executor for each exact plan path, requires uncached executed case events and
writes the report before returning. Compile that entrypoint with an admitted
toolchain and pin its binary as the task producer. Its cwd is the existing
`<attempt>/work`, with the immutable request one directory above it. Include the
admitted native compiler at pinned `tools/simple`, all spec inputs, the plan and
policy in the task input closure. The task arguments select the exact ordered
paths and native mode. The wrapper selects the pinned compiler, one worker,
fresh builds and actual-case events; it does not discover a fallback compiler.

The reporter consumes the existing TraceRunPlan and actual framework
start/finished events. It refuses missing, duplicate, unknown, pending and failed
cases. A missing report is never retrofitted after the generic worker failed.

Container mode uses the shared Simple Container API, with Podman on Linux and
Docker on Windows. Its completion signer must consume container-owned cleanup
and absence proof plus exact runtime identity and bytes. Neither the native
worker adapter nor a host start/inspect observation proves container completion.

Before qualification, run the source specs and real native/container provider
smokes with an admitted runtime; sabotage signatures, fences, toolchains,
outputs, per-case reports and cancellation timing. Measure request latency/RSS
at the documented 4 MiB wire limit. Generate and review SPipe manuals, then run
the repository verifier. Source-authored manuals and orderly reopen scenarios
must not be reported as executed tests or a crash/power-loss qualification.
