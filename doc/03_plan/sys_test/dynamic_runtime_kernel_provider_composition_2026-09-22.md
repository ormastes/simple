<!-- codex-design -->

# Dynamic runtime/kernel provider composition — test plan

Status: implementation handoff, not executed acceptance. Reuse existing specs
and add only missing scenarios in the owning lane. No generated manual or
SPipe PASS is claimed by this documentation-only change.

## Traceability and evidence

Requirement IDs below are scoped to their linked parent requirement document;
they do not create a competing numbered requirements set.

| Existing requirement | Scenario and required assertion | Primary owner |
|---|---|---|
| Runtime REQ-001/003, NFR-005 | No-import hello maps/initializes zero optional providers; link receipt names retained roots | runtime closure |
| Runtime REQ-002/012/013, KPM-REQ-004/006 | Real native provider executes; missing/changed/wrong-target/wrong-ABI artifact rejects before execution | loader/bootstrap |
| Runtime REQ-004/005/006 | Static/dynamic provider outputs and failures agree; effectful operation executes once; promotion uses retained evidence | provider |
| Runtime REQ-007–011/014/015 | Existing size/profile/cohort suite proves noalloc/NoGC closure and sealed provider availability, retains maps/hashes | runtime closure |
| KPM-REQ-001/002/003/005 | K0-to-P forbidden import, changed typed ABI field, invalid parameter header and direct hot env read each fail checker | kernel contract |
| KPM-REQ-007/008/010/011/012 | Provider-body edit leaves kernel object key stable; K0 edit invalidates; selected backend/ABI/manifest policies enforced | composition |
| KPM-REQ-009 | Positive fixture and injected mutation run through the same admission/checker | every lane |
| KPM-REQ-013/014 | Preserve existing APK-only coverage and bounded lock-range tests; no altered acceptance inferred here | existing migration owners |
| KPM-NFR-001/002/004 | Metadata overhead <2 ms; no per-node negotiation; pure-Simple bootstrap continuity retained | bootstrap/perf |
| Environment NFR-002/003/005/007/009 | Named selection/batch/RSS/capacity fixtures meet selected thresholds; CPU-only startup does not initialize GPU | variant owner |
| Environment REQ-002–007/012–016 | Existing owner fixtures distinguish host/target, validate exact descriptor/registry/inspector authority, reject incompatible candidates, preserve deterministic bindings and typed placement, and retain generation/receipt evidence | variant/loader owners |
| Existing aspect mapping/lifecycle contracts | Distinct mapped payload result and joined mapping/generation lease; stale final-unpin fails; live callback blocks retirement | aspect owner |
| Cocoa sole ownership / P0 integration | Exact admitted cdylib exports all 12 registered `rt_cocoa_*` signatures; runtime rlib/staticlib and native-all archive definitions absent; mutate cdylib while archive stays fixed and admission fails | macOS/bootstrap |

Parents:
[runtime](../../02_requirements/feature/runtime_optional_provider_binary_size_optimization.md),
[kernel](../../02_requirements/feature/kernel_plugin_migration.md),
[kernel NFR](../../02_requirements/nfr/kernel_plugin_migration.md),
[environment feature](../../02_requirements/feature/environment_optimized_dynamic_libraries.md),
[environment NFR](../../02_requirements/nfr/environment_optimized_dynamic_libraries.md).
Outstanding aspect requirement choices remain outside an acceptance verdict.
Untouched parent requirement gates remain in force; these integration scenarios
neither replace their full coverage nor establish a parent feature PASS.

## Existing executable anchors

- `test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl`
- `test/03_system/compiler/feature/kernel_plugin/kernel_plugin_lifecycle_placement_parity_spec.spl`
- `test/03_system/compiler/feature/kernel_plugin/k0g_import_closure_spec.spl`
- `test/03_system/compiler/feature/kernel_plugin/cross_placement_semantic_conformance_spec.spl`
- `test/01_unit/compiler/loader/aspect_lifecycle_gate_native_runner_spec.spl`
- `test/01_unit/lib/aspect_pack_final_unpin_v2_spec.spl` — current `ApkFinalUnpinLeaseV2` contract candidate; no execution result claimed here.

Historical reference only:
`test/01_unit/compiler/loader/aspect_final_unpin_registry_spec.spl` is explicitly
**AUTHORED-UNEXECUTED** and refers to an absent registry module and older
stage/commit helpers. It is not executable coverage for the current owner.
Current lease/native lifecycle specs still do not independently prove mapped
advice execution or physical unmap; the integration gates above must join them.

Proposed integration spec, only when executable helpers are implemented:
`test/03_system/compiler/feature/kernel_plugin/dynamic_runtime_provider_composition_spec.spl`.
Its manual mirrors into `doc/06_spec/03_system/compiler/feature/kernel_plugin/`.
Do not author a source-text-only check and label it native execution proof.

## Shared scenario vocabulary

Freeze manual steps before parallel authoring:
`step("Start with no optional provider demand")`,
`step("Admit the exact runtime provider")`,
`step("Invoke the mapped provider payload")`,
`step("Reject a changed provider artifact")`,
`step("Drain the generation before retirement")`.

Planned helpers: `setup_provider_composition_fixture`,
`check_no_optional_provider_loads`, `check_admitted_provider_identity`,
`check_mapped_payload_result`, `check_changed_artifact_rejected`,
`check_generation_retirement_blocked`. Helpers must fail with `assert(false)`
or `fail(...)` until real behavior exists; placeholder specs cannot pass verify.
Capture binary, exec and protocol evidence, including hashes, result values and
rejection codes. Use built-in matchers and review generated manuals with zero
stubs before accepting the implementation.

## Qualification protocol

Run native macOS ARM64 first on this host, then native macOS x86_64, Linux,
Windows and supported FreeBSD fixtures. Cross-format inspection or emulation
does not prove native invocation/performance. SimpleOS uses its admitted SMF/
kernel loader and separate boot authority; a hosted dlopen test cannot cover it.

Runtime-provider performance takes 30 development/100 release samples with
p50/p95, RSS, compiler/tool/provider hashes and same-host baseline. Preserve
environment-variant p99 and declared fixture qualification. First-use mapping,
constructor/init, selection and hot invocation are separate measurements.

For changed compiler/lib code, the integration owner runs required compiler,
lib, MCP/LSP checks and MCP interpreter/native smoke once on an admitted
self-hosted runtime, plus direct-env guards. Documentation alone does not
trigger bootstrap or broad compiler tests. At most three fix/verify cycles;
retain failures and stop that gate instead of repeating green checks.
