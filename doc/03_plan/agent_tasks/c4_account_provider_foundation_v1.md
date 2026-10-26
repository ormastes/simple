# C4 account/provider foundation and next owner task

Parent lane: complete the selected robust plan on `release_phase3`.
This packet lands reviewed account/provider leaves as a foundation; full
FORMAL-PHYSICAL-ACCOUNTING remains OPEN. See
[integration and provenance](../../05_design/compiler/c4_account_provider_foundation_v1.md).

| Lane | Owner | Deliverable |
|---|---|---|
| Selected-scope reuse and current dependency audit | Astra current-target auditor | Retained `/tmp/physical_provider_accounting_research_20261025.md` |
| Account/provider integration | Codex `sol_c4_provider_account_impl` | Four leaves, three actual API SSpecs, three authored manuals, current 36-field adaptation |
| Independent source review | Astra `astra_static_lock_level_guide` | Exact imported/adapted delta and evidence-boundary review |
| Lower-model sidecars | N/A | Existing reviewed components reused; no new generated sidecar findings |
| Merge owner and final reviewer | Root coordinator / Astra | Scoped commit review before publication; no child push/PR |

## Required next SOURCE task

Reuse B/source-producer-component/revision2 and the selected shared-construction
design, with B defined in the integration doc. Compare current dependencies and
actual constructors before importing any source packet. The existing
`hir-source-admission-implementation-v1` packet is incomplete and includes nine
intentional fail-fast helpers; it must not be imported as a passing feature.

Implement the frozen `lower_module_loop_view_v1(module, target, account)` entry
at actual source construction, before rich return. Preserve the ordinary route.
Never implement it as `view(lower_module(...))` or charge a returned graph after
construction. Capture and reserve signature/type, locals, instructions,
terminators, declarations, predicates, loops, source spans and every replacement
revision at their owning constructors. Any bypass must fail the opted invocation.

Classify current no-GC/short metadata from actual source or reject unsupported
cases; the neutral planner projection does not admit it. Preserve generated
visitors and all current shared dependency fields. SOURCE must publish a complete
current-field/hook inventory before sealing can establish source authority.

Compose the same account through checked PLAN, context, EMIT, attempts, relations,
diagnostics and evidence. Reserve actual retained-capacity/copy descriptors for
every handoff before growth. Authentic native type/scope transfer descriptors,
complete physical storage provenance, post-seal clone certification, and full
runtime/backend provider parity remain open implementation gates. Do not invent
byte constants, new limits, runtime ABI or weaker positive semantics to close them.

Final acceptance needs actual SOURCE→view→checked plan→emitter→artifact execution,
exact/one-under failures before allocation, unchanged ordinary-route behavior,
native owner/alias/close/privacy and capacity evidence, bounded runtime/RSS, and
independent review. Keep invariant/termination status UNPROVED, formal NOT_CHECKED
and native UNPROVEN until their separate proof gates pass.
