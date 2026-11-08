# Neutral exec request and birth receipt integrity

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 exact immutable association; HOST-02 parent/native identity.
Spec: `test/03_system/app/orchestrator/feature/container_exec_v3_spec.spl`.

Setup: construct Linux native-boot and Windows service-incarnation parent plans,
full observed-shaped parent runtime identities (including full native CID), and
neutral exec requests. Include a literal and an unresolved versioned secret
reference. Construct a separate full64 exec ID and birth receipt. These are pure
integrity fixtures: no owner, engine response, native birth or authorization is
fabricated. Both request and receipt bind the exact parent CID; changing CID
changes the request digest and prevents reuse of a prior receipt.

| Exact step | Procedure / checks |
|---|---|
| round trips Linux and Windows requests with literal and unresolved secret entries | Round-trip both platform shapes; preserve ordered argv, neutral environment entries and provider-call timeout. |
| binds scope operation nonce argv and every environment value or secret version | Change authorized alias, machine, service, generation, boot, exact parent CID, exec operation, nonce, argv, literal or secret version. Each valid changed association changes digest. |
| round trips correlated birth without retaining request arguments or secret references | Round-trip both births and require full request/parent correlation. Receipt excludes argv and secret-reference strings and uses distinct parent/exec IDs. |
| refuses parent container id as exec id and every mismatched parent identity | Refuse equal or short native exec ID and mismatched parent CID/UID/attempt/operation/generation/engine/fence/request digest. |
| refuses wrong platform users paths and malformed execution options | Refuse noncanonical Linux numeric uid:gid, Windows administrator/drive-relative executable, relative cwd, reused parent operation, unsupported terminal and nonpositive timeout. |
| rejects duplicate environment names literal overflow and malformed secret references | Refuse duplicate names including Windows case-insensitive collisions, invalid names, literal UTF-8 overflow, multiline secret reference and invalid version digest. |
| rejects unknown duplicate mistyped and noncanonical request and birth wire | Refuse unknown authority fields, string stdin flag, duplicate/noncanonical request, leaked environment field in birth and string timestamp. |
| bounds request and birth bytes without granting workload lifetime control | Refuse request over1MiB, birth over16KiB, and empty argv. No timeout or disconnect can establish exec termination. |

Request v3 SDN includes every known field and nested canonical parent plan/runtime.
Environment remains neutral: literal values are bounded at16384 bytes; secret
references are bounded at1024 bytes and version-hashed, never resolved. Windows
initial policy permits exactly ContainerUser; Linux requires canonical nonnegative
numeric uid:gid. Raw64 nonce/query/evidence/provider/native IDs retain their
explicit roles. Exact re-encoding rejects unknown, duplicate, missing, wrong-type
and noncanonical data. Bounds use str_len bytes, not Unicode character counts.

The request timeout is ONLY a bounded provider control/observation/transport call
window. It is not workload duration, Engine exec-stop capability, PID control or
auto-kill authority. Admission expiry is a separate effect deadline. Helper timeout
or disconnect does not prove exec ended; running/unknown work remains charged.
A birth-shaped object proves no native creation or authority. Actual platform
producer must observe one native exec ID; uncertain creation never auto-retries
with a new ID. Parent host/provider authorization and cleanup remain separate.
Builds and test execution were prohibited for this source task.
