# Common host execution contract specification

Status: **NOT_RUN / AWAITING_DEPENDENCIES**. Authored manual, not generated evidence.

Executable: `test/03_system/app/orchestrator/feature/host_execution_common_contract_spec.spl`.
Fixture: `test/fixtures/orchestration/host_execution_envelope_fixture_v2.spl`.
Design: `doc/05_design/host_authorized_execution_v2.md`.

| Requirement | Authored case |
| --- | --- |
| HOST-EXECUTION-COMMON-01 | Strict original V1 packet normalizes runtime routing using trusted native scope while original signed plan/operation remain unchanged; actual signatures verify; legacy service-incarnation normalization refuses |
| HOST-EXECUTION-COMMON-01 | V2 packets for exact Linux/Podman native mode and Windows/Docker-process service mode bind original plan and full opaque scope fences; real signatures verify; noncanonical packet and trusted-native-machine alias mismatch refuse |
| HOST-EXECUTION-COMMON-02 | Real private filesystem stores original created native intent for Podman/Docker, checks mode0600/readback, refuses native-ID or later-phase replacement |
| HOST-EXECUTION-COMMON-02 | Canonical UTF-8 size/type/native-ID/engine intent bounds reject malformed or incomplete evidence |
| HOST-EXECUTION-COMMON-02 | Separate ObservationV2 accepts only Podman/Docker with explicit native/service scope and runtimeFenceId; fake native labels and scope replacement refuse; real private original/archive and guarded inspection-cache roundtrip preserve original bytes |

The envelope fixture intentionally carries an opaque shape-only request body; it is NOT a provider request or runtime admission. Real Ed25519 signatures attest these shape-test envelopes only. No actual container owner, engine observation, native launch or completion result is synthesized.

Missing dependencies: common execution/deadline contracts, common facade and execute V2 envelope source are frozen but absent from this worktree. The actual common-owner enum/real-adapter explicit fixture seam is now known and all eleven lifecycle scenarios are converted in the separate lifecycle spec; root dependency import is pending before execution. No build/compiler/SSpec/provider command has run, and no platform qualification is claimed.
