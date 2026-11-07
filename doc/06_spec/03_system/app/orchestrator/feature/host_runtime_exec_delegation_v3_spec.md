# Exec DATA delegation and control metadata hash

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 original parent/install association; HOST-02 retained effect origin.
Spec: `test/03_system/app/orchestrator/feature/host_runtime_exec_delegation_v3_spec.spl`.

Setup: actual child/request and installation codecs use canonical nested intent,
parent/controller references and existing real signed frames strictly as DATA.
A canonical minimal policy dictionary is accepted only as generic installation
wire shape; it is NOT a provider-ready installed policy. Construct recorded begin
sequence/commit digest, positive historical observation time and exec-only raw
request deadline. No actual journal BEGIN, native query, protected origin or
installed loader is mocked or certified by a positive codec result.

| Exact step | Procedure / checks |
|---|---|
| round trips exact child installation recorded begin facts and deadline without constructing admission | Round-trip full canonical delegation; preserve child and installation packets and hash the entire packet with no selfhash field. |
| refuses rebound installation artifact baseline and exact scope mismatches | Refuse installation packet-hash instead of intent-artifact hash, and scope/baseline mismatches even after rehashing installation intent/operation. |
| refuses changed child original parent or controller provenance despite rebound child hash | Tamper original parent or controller digest, rebind child intent hash, and still refuse inconsistent parent assignment provenance. |
| requires positive recorded begin and observation before exact raw exec deadline | Refuse zero begin sequence, invalid commit hash, nonpositive or expired recorded observation, intent-hash deadline instead of raw exec hash and widened actions. |
| hashes all metadata runtime and scope fields while refusing malformed profile and native identity | Change query/evidence/time/runtime/op/attempt/provider/control/policy/request/fullscope fields; observation hash changes. Refuse short CID and unsupported API. |
| binds exact child proof expiry and distinct host journal operation identities | Refuse either widened or narrowed expiry relative to the forwarded frame minimum; refuse installation IDs colliding with child or parent even after rebinding the installation hashes. |
| refuses unknown typed duplicate noncanonical missing and overbound delegation wire | Refuse unknown authority claim, string sequence, duplicate/missing/noncanonical fields and over4MiB UTF-8 wire. |

container_exec_control_observation_digest_v3 canonicalizes ALL metadata fields,
full7field runtime and full scope bytes. It validates explicit Linux5.2.5 and
Windows1.48 profiles, raw hashes, positive clock, full native CID and scope fence.
No decoder, fake query receipt or reconstructed native owner is introduced.

Delegation reuses existing canonical child, SDK proof and Host installation
codecs; installation_artifact_digest hashes canonical installation INTENT, not
its proof packet. Exact scope fence and installed parent-provider baseline match
the child. Positive begin sequence/commit/control hashes and recorded time before
raw-exec/op/exec-only deadline are structural data checks only. Decoder never
reads a fresh clock, verifies SDK authority, opens another journal, reconstructs
ContainerExecAdmissionV3 or grants an effect. Actual broker MUST resolve retained
BEGIN and protected origin, verify fresh signed proofs, reload installed policy
and correlate actual control observation/native owners before admission.
The broker must recompute the minimum verified child grant/approval expiry and
compare it with the recorded deadline. Recorded observation time is never a
substitute for the actual current clock. Native one-use claims are keyed by
scope and child operation independently of the helper launch root.

The structural codec also requires the recorded deadline to equal the minimum
expiry in the forwarded child frames and keeps installation, child and parent
Host operation IDs distinct. This does not verify those frame signatures.

The full delegation digest is SHA256 of canonical packet;4MiB outer uses str_len.
Nested codecs keep their own limits; escaping overhead may reject combinations
rather than truncate. Host installation dependency is referenced read-only, not
copied. No runtime execution was performed; actual runtime remains NOT_RUN.
