# Retained workspace preparation stage integrity

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 immutable stage association; HOST-02 exact owner resolution.
Spec: `test/03_system/app/orchestrator/feature/container_workspace_preparation_v3_spec.spl`.

Setup: construct actual-codec Linux exec intent and matching birth-shaped data,
then bind distinct workspace-stage operation, parent/assignment/storage/workspace/
mapping digests, disjoint lexical input/output roots and allowlisted executable
hashes. These are pure integrity fixtures, never native observations or actual
quota/mapping/root/exec authority. No fake owner/provider replaces a consumer.

| Exact step | Procedure / checks |
|---|---|
| round trips every binding and exact exec request birth and manifest | Round-trip full canonical stage; preserve nested exec/birth bytes, manifest and stage digest distinct from exec digest. |
| binds mapping storage and executable bytes without conflating their digests | Change mapping receipt digest, storage reservation or executable bytes; stage digest changes. Invalid mapping binding digest is refused. |
| refuses reused stage operations mismatched births and unsupported backend profiles | Refuse parent/exec operation reuse, changed parent CID in birth, invented mount profile and Windows backend even with valid Windows exec/birth. |
| refuses lexical root escapes overlap and platform absolute paths | Refuse empty/absolute/drive/dot/dotdot/backslash/control/repeated-slash/trailing-slash/overlong roots and equality or either ancestor overlap. |
| permits only bounded exact executable manifests without chmod modes | Refuse empty, arbitrary-path, duplicate-path or malformed-digest manifests. Only producer.exe and tools/simple are allowed; no chmod mode exists. |
| rejects unknown missing typed duplicate noncanonical and oversized stage wire | Refuse unknown chmod field, mistyped nested birth, old version, missing required fields, duplicate version, extra newline and over2MiB UTF-8 source. |

Only linux-build-input-output-v1 with linux-podman is implemented. Relative-root
validation is lexical; actual native consumer must prove root identity, aliases,
quota, immutable keeper, RO input/RW output and live mapping/intended exec user.
The mapping_receipt_digest means container_user_mapping_receipt_digest_v3 of the
FULL retained receipt, including all scope/request/provider/pre/post associations;
it is not receipt.native_evidence_digest alone. mapping_binding_digest must equal
that receipt.native_binding_digest. Host/common live consumer must resolve both to
the full receipt, verified producer provenance and retained native owner. This
pure codec deliberately does not import or impersonate the mapping owner.

The host resolves exec_intent_digest to the original signed HostRuntimeExecIntentV3
in the SAME journal and recomputes its hash, preserving the separate baseline and
exec-control pins and original controller envelope association. It resolves every
parent/storage/workspace digest to real retained owners,
then authorizes a fresh signed workspace_prepare_v1 in the SAME journal. Only the
completed retained stage permits exec start; authorized exec birth may already
exist first. Stage digest is neither workload digest nor mapping authority.
Deadline is separate and is not fabricated/imported here. Exact canonical SDN,
known-field/type/duplicate checks, birth matching and2MiB str_len bounds establish
integrity only. Builds/tests were prohibited for this task.

File hash and mount checks do not prove absence of privilege-changing executable
xattrs. The actual preparation/start path must reject those attributes or enforce
a qualified no-new-privileges execution policy before claiming user preservation.
