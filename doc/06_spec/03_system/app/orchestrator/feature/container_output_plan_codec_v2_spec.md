# Canonical retained container output plan

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 immutable correlation; HOST-02 retained scoped output intent.
Spec: `test/03_system/app/orchestrator/feature/container_output_plan_codec_v2_spec.spl`.

Setup: construct a full typed output-follow plan with all seven runtime identity
fields, six parent/helper identity fields, exact workload/scope, positive resources,
provider/policy digests and complete V3 launch template/profile. The template has
zero transport generation and zero launch deadline. This is a pure integrity
fixture, not a provider or owner. Constructor/schema and encode/decode function
names were checked against immutable daemon commit
`29dc76e6834938228b26c765b87ec03da60c8cd4`; that dependency is not copied here.

| Exact step | Procedure / checks |
|---|---|
| round trips the full template runtime identity and parent association without changing digest | Round-trip canonical outer bytes; preserve original digest, full daemon template bytes, runtime/parent identities, resources and workload bytes. |
| refuses changed digest template engine and runtime fence before restoration | Refuse stale request digest after template change, wrong engine/fence, and malformed nested template wire. |
| refuses generated transport and deadline fields in a retained template | Refuse nonzero generated transport generation and launch deadline before encode. No invented expiry normalizes a retained plan. |
| refuses unknown missing mistyped duplicate and noncanonical outer fields | Refuse unknown authority claim, missing budget identity, string runtime attempt, old version, extra newline and duplicate version. |
| bounds total and nested encoded bytes without accepting partial templates | Refuse empty/over-2MiB total UTF-8 input and oversized nested template without partial acceptance. |

The existing ContainerOutputPlanV2 fields and digest algorithm are unchanged.
Outer version2/kind container-output-plan stores every full field; template bytes
are exclusively the daemon canonical V3 codec, and workload uses its existing
canonical plan codec. Encoder recomputes request_digest; decoder revalidates all
plan/template rules and requires exact re-encoding. Total and individual encoded
nested strings are capped at 2 MiB via str_len; escaping can make nested-valid
inputs exceed the outer cap and fail, never truncate. Restored data is integrity
only. Common open still requires a fresh actual plan and verified host helper
lease/admission; no wire decoder for ContainerHelperAdmissionV2 is introduced.
Builds/tests were prohibited. Combined daemon dependency and platform qualification
remain separate root integration gates.
