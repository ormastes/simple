# Container service quarantine and selected-user integrity

Status: **NOT_RUN**. Authored scenario manual; no runtime or generated PASS evidence.
Executable: `test/03_system/app/orchestrator/feature/container_service_user_v2_spec.spl`.
Requirements: ORCH-02 (fenced correlation), HOST-02 (retained host evidence).

Setup: import the actual common service, execution and evidence contracts. Construct
an authorized alias separate from a native Windows machine GUID, an old service
incarnation, a charged inventory row with full native ID, and a selected-engine-user
receipt. These are pure data fixtures; no SimpleContainerOwner, provider, native
query, host journal commit or effective workload UID is fabricated.

| Step / exact executable case | Procedure and required check |
|---|---|
| accepts old same machine inventory and binds the new owner epoch | Hash an old-scope row under old and new owner incarnations; accept same-machine old epoch, change inventory and scope hashes; empty inventory has only structural meaning. |
| rejects duplicate native identities and duplicate operations independently | Change only operation while retaining native ID, then only native ID while retaining operation; reject each duplicate independently; accept both unique. |
| refuses alias machine scope charge and unsupported mode collisions | Alter native machine, authorized alias, service scope, zero CPU or negative memory; reject all. Refuse Linux backend and native-boot mode for the Windows service route. |
| requires exact journal acknowledgment shape and process crash durability | Accept revision zero only with empty commit digest; accept positive revision with digest syntax; refuse empty positive commit and unsupported power-loss profile. This does not prove a real commit. |
| round trips both selected user receipts and binds exact query argv boundaries | Round-trip both backend receipts; changing selected user changes digest. Hash argv arrays with equal joined text but different argument boundaries and require distinct digests. |
| refuses selected user identity scope provider pin and proof shape tampering | Refuse short native ID, changed incarnation with stale runtime fence, empty operation, invalid provider pin/query digest and invented effective-UID proof kind. |
| enforces selected user byte bounds and rejects control characters | Accept exactly 256 UTF-8 bytes; refuse 258 bytes, empty user and NUL/newline/carriage-return/tab characters. |
| rejects unknown duplicate typed noncanonical and oversized receipt wire | Refuse unknown authority claims, string timestamp, extra newline, duplicate version and 65538-byte wire. |

Checks exercise canonical integrity and typed correlation only. Syntactically valid
query/evidence/provider digests are supplied values, not authenticated observations.
The selected engine user does not establish effective UID, token, privilege or native
authority. Production platform tests must execute the actual engine query; the host
must correlate actual retained startup receipt and its independently owned journal
before admitting a quarantined owner. No platform execution or service recovery PASS
is claimed here. Builds and test runs were prohibited for this authoring task.
