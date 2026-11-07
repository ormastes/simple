# Orchestration scalar type boundaries

Status: **AUTHORED — NOT_RUN / AWAITING_VERIFICATION**. This manual describes
executable assertions; it is neither generated output nor runtime evidence.
No compiler, test, docgen or build command was executed for this change.

Source: `test/03_system/app/orchestrator/feature/resource_scalar_types_spec.spl`.
Requirements: CFG-01, CFG-02 and REQ-ORCH-01-A.

The eleven examples distinguish strict text fields from quantity fields:

| Example | Authored assertions |
| --- | --- |
| Nontext metadata | Integer, boolean, null, float, array and dictionary values reject at name/namespace with type, path and exact original coordinates. |
| Explicit identity text | Quoted numeric names/namespaces remain text; integer profile CPU and memory retain canonical quantities. |
| Quantity equivalence matrix | Decimal string and integer quantities agree for 0, 1, 2 and 64; CPU scales to millicores and memory stays bytes. |
| Nonquantity variants | Boolean, null, float and collection quantities reject at exact CPU/memory field coordinates. |
| ResourceList child | An invalid child name reports the prefixed child path and original document coordinates. |
| Pod commands | Valid textual commands decode; integer command elements reject at the element path and source position. |
| Deployment references | Valid text artifact references decode; integer references reject with exact field coordinates. |
| CI commands/references | Valid Job and Pipeline decode; integer Job command elements and Pipeline template references reject. |
| Shared helper boundary | Only String crosses strict as_text; quantity conversion additionally permits Int. Other SDN variants reject. |
| Wire identity | A valid canonical launch plan preserves its workload identity; integer workloadUid rejects as type before canonical-byte comparison. |
| Workload integer quantities | Bare integer requests/limits remain accepted and retain exact CPU/memory values. |

`assert_scalar_rejection` computes expected positions from the authored source
lines and field spelling, independently of decoder span records, then asserts
error kind, exact schema path, line and column. The ResourceList case ensures
child dispatch does not replace original source positions.

The production change makes `as_text` String-only and introduces
`as_quantity_text` for String-or-Int quantities. Its only quantity callers are
workload resource CPU/memory and ResourceProfile amounts. Remaining shared
text consumers retain strict string semantics: envelope versions/kinds,
metadata names/namespaces/labels, OS/runtime identifiers, image/artifact
references, commands/arguments/ports, CI names/template references/dependencies/
run policy, configuration identities, digest/fence fields and launch-plan text. The shared
consumer audit also includes desired-input IDs/digests, agent-policy snapshot
digests, assignment records, host reservation codecs (including exclusive-device
IDs), prepare responses, execution kinds, workload-fence codecs and container
bound-intent V2. Those fields remain semantic strings, not quantities.
No decoder is authorized to stringify arbitrary integers as identity text.

All examples remain NOT_RUN. Qualified pure-Simple full CLI/runner execution,
positive executed-example counts, compiler/runtime/source identities and
matching generated-manual evidence are required before a verification PASS.
The user limit remains five aggregate CPU cores; this authored document does
not authorize a build or test launch.

## Current decoder inventory correction — 2026-11-07

At source `862d9e361534c1a13f83a2f43da06e07847df5af`,
`src/lib/common/contracts/orchestration/resource_set_v1.spl` dispatches
HostConfig, HostPool, RuntimeClass, AgentSession, ResourceProfile,
Pod/Deployment and Job/Pipeline, including nested ResourceLists. Its
`decode_item` branches and `ResourceSetItemV1` variants establish that these
decoder kinds exist in source. The older requirement inventory's statement
that other configuration kinds are pending describes its historical checkpoint;
the historical prose is preserved, not treated as a current source inventory.

This correction does not certify strict admission for every field, reference
resolution, immutable execution plans, or end-to-end controller/provider
behavior. The numeric-to-text coercion fixed here and missing indexed block-list
diagnostics were concrete gaps despite the kinds being present. Resource-profile
range ordering and whole-exclusive GPU placement already exist in source;
the accompanying tests add scalar and device-admission coverage. Runtime
qualification, actual SSpec execution and generated-manual evidence remain
pending on compatible pure-Simple tooling. All schema requirements are not
declared complete by this source inventory.
