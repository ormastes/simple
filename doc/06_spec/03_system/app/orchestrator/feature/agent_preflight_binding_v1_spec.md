# Expected AgentSession preflight association

Status: **NOT_RUN**. Authored manual; no generated or runtime PASS evidence.
Spec: `test/03_system/app/orchestrator/feature/agent_preflight_binding_v1_spec.spl`.
Requirements: ORCH-02 immutable desired-state correlation; HOST-02 exact scoped input.

Setup: import the actual common binding and V2 plan codecs. Construct separate
session/preflight workload UIDs and immutable expected source/catalog/task/image/
probe-producer/nonce digests. Use native Linux and persistent Windows scope shapes.
No container owner, actual image probe, installed CLI or observed user is fabricated.

| Exact step | Procedure / checks |
|---|---|
| round trips both execution platforms without claiming observed capability | Encode/decode both platforms and compare canonical bytes; session and preflight workload remain distinct. |
| binds image nonce and exact scoped request plan into the payload digest | Independently change image, nonce, request digest and native machine; each changes payload digest. |
| keeps one operation id per controller session while refusing silent payload replacement | Change nonce for same controller/session; operation ID stays stable and payload changes. Independent lookup ID agrees, metadata domain/host/payload are exact, invalid controller is refused. Actual journal conflict handling belongs to the consumer. |
| refuses same session preflight identity and incompatible provider platform architecture | Refuse same UID, incompatible OS, unknown agent, amd64 alias and malformed probe digest; accept policy-supported aarch64. |
| requires execution OS absolute executable paths and bounded selected user bytes | Refuse relative/root/dotdot/control paths and Windows drive-relative paths; accept 256 UTF-8 user bytes and refuse larger/empty/control values. |
| refuses unknown duplicate mistyped noncanonical and oversized wire | Refuse unknown observed claim, numeric nonce, string version, duplicate version, extra newline and 65538-byte source. |

The canonical ID hashes a domain-separated SDN object containing version, kind,
controllerId and sessionUid only. The binding payload includes every expected
field and exact canonical V2 plan. Unit metadata envelope memory/duration values
are schema placeholders matching the established metadata domain, never grants
or physical charges. The actual service boundary owns authorization and its
existing controller journal owns admission/conflict/recovery. This contract does
not authenticate evidence, resolve image tags, prove CLI capability, authorize
selected user or execute any preflight. Builds/tests were prohibited for this task.
