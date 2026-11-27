# Host preparation replay admission

Scope: HOST-02 / ORCH-02 durable local capacity ownership. This source slice imports the existing host capacity projection, immutable reservation codec, and single-writer owner from the concurrent orchestrator lane. It does not introduce a cluster scheduler or change TaskRunnerV1.

## Defect and behavior

The pure projection intentionally retains identical reservation identities in every lifecycle state. Its successful duplicate result means the stored state is unchanged. The durable owner previously interpreted that result as a successful prepare response, including after expiry, prepared abort, execution, or uncertain recovery. A caller could therefore receive a misleading fresh prepared receipt.

For a journaled duplicate, the owner now uses its existing prepared-receipt verifier before returning success. That path checks the exact envelope and retained payload, admitted journal state, continuity, and the strict deadline. It rejects before payload publication or journal mutation. Fresh admission continues through the existing V2 commit. Live replay keeps the same journal sequence and charge. Expiry and execution uncertainty never release resources. A confirmed prepared abort retains its identity and released state.

## Boundaries

`host_capacity_v1` owns pure capacity candidates and host/boot/provider fences. `host_capacity_owner_v1` owns the local journal, retained intent, prepare/begin/abort/expiry and conservative recovery projection. `operation_dispatch_v2` supplies shared journal mechanisms. `distributed_operation_state_v2` remains the sole operation state machine. Authentication is performed by the existing authorized service boundary; raw grants supplied to the internal owner are trusted inputs, not remote authentication.

The imported owner exposes no daemon listener, enrollment, application entrypoint or container execution effect. This slice does not establish daemon SDK transport, actual Podman cleanup, provider absence receipts, session mux integration, full reconciliation across changed boots, or platform execution qualification. Failed preparation must not imply native work was absent.

## Verification contract

The real-journal fixture covers live idempotent retry, exact-deadline refusal, aborted retry, executing retry and close/reopen outcome-unknown. It checks resource charge and journal immutability, with additional continuity and host-fence refusal. Runtime status remains NOT_RUN until the exact fixture executes using a recorded toolchain. Static source review is not runtime PASS.

Source provenance is recorded in `doc/05_design/host_prepare_replay_provenance.sdn`. The main workspace is read-only; unrelated compiler, database, IO and provider work is excluded. Astra owns final review; one Sol worker implements the scoped owner fix and regression fixture.
