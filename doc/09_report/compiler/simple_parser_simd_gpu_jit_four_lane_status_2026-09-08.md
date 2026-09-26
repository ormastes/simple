# Shared parser, GPU, SIMD, and generated-code status

**Status authority refreshed:** 2026-09-26. This report repairs the missing
status target referenced by
`doc/03_plan/compiler/environment_optimized_dynamic_libraries.md`. It records
source-level evidence and the next promotion gates; it is not a verification
PASS or a claim that a provider executed.

## Four workstreams

| Workstream | Current source evidence | Completion verdict | Next authoritative gate |
|---|---|---|---|
| Shared parser | `src/compiler/10.frontend/core/frontend.spl` defaults to `LegacyReference`, rejects every candidate in `parser_provider_v1_admit`, and reports the Simple grammar/action prerequisite unavailable. `src/lib/common/structural/parse/` and `src/lib/nogc_async_mut/structural/parse/` contain shared contracts and lexical/scalar infrastructure. | Incomplete. No canonical Simple AST/HIR provider, nor qualified Simple/SDN/sosh dialect parity. | Execute a distinct canonical scalar Simple grammar/action engine and compare reset, append, isolated errors, tokens, regions, HIR actions, source mappings, diagnostics, invalidation, and deterministic hash against the legacy oracle before admission. Qualify SDN and sosh separately. |
| GPU parser | `src/compiler/00.common/structural_contracts/frontend_offload_switch.spl` fixes `FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE` to `false`; the driver consumes that gate. The native GPU provider substrate described in the dynload plan does not itself connect a packed parser batch. | Incomplete. Provider admission and retained completion cannot prove parser GPU execution. | Bind an authenticated parser device program to a task owner, submit a real parser batch, read back and compare ordered output, retire its fence/resources, and pass absent-device, wrong-program, loss, and spoofed-completion controls. |
| SIMD parser | `src/compiler/99.loader/parser_lexical_mask_call_native_v1.spl` wraps one native 32-byte lexical mask callable. `src/lib/nogc_sync_mut/composition/environment_variants/feature_registry_v1.spl` now admits the exact declared V1 VBMI/VBMI2 union; `test/01_unit/lib/nogc_sync_mut/composition/environment_variants/feature_registry_vbmi_boundary_spec.spl` contains direct boundary assertions. | Incomplete. A lexical primitive and feature metadata do not make the Simple parser a SIMD provider. | Prove exact scalar/candidate parity for the complete parser, emitted and executed ISA on compatible hardware, tails and guard pages, parser-only artifacts, and the selected NFR speedup. |
| Generated JIT/AOT/dynlib SIMD | `src/compiler/80.driver/parser_variant_build_plan_v1.spl` is an inert plan with no production caller found in `src/`; `src/lib/nogc_sync_mut/composition/environment_variants/target_codegen_profile_v1.spl` separates host and target facts. The dynload plan says sibling emission, target-aware JIT materialization, canonical cache V2, and ISA execution evidence remain open. | Incomplete. Planning identities are not built, loaded, or executed siblings. | Qualify canonical bounded cache material and authenticated backend feature acceptance; build exact sibling/JIT units, inspect their complete executable closure, invoke a pinned callable, compare with scalar, and verify cache invalidation and rollback. |

## Cross-lane release boundary

The selected feature requirements are in
`doc/02_requirements/feature/environment_optimized_dynamic_libraries.md`.
Promotion must also satisfy the SOSIX service/retirement boundary and the
SimpleOS immutable-candidate, cold-boot, compiler-in-guest, and persistence
requirements in `doc/02_requirements/feature/simple_platform_unification.md`.
The proposed SOSIX unification design at
`doc/01_research/runtime/sosix_unification/simple_sosix_runtime_unification_design_plan_2026-09-05.md`
is not implementation evidence. None of those cross-lane release gates is
closed by the four source-presence observations above.

## Verification status and next action

No current pure-Simple end-to-end acceptance result was available to this
reporting pass. The macOS test-runner crash is tracked in
`doc/08_tracking/bug/macos_test_runner_monitor_spawn_crash_2026-09-26.md`;
bootstrap-seed diagnostics cannot close product gates. The next product-critical
unit is the canonical Simple grammar/action provider and its differential
corpus. GPU, SIMD, and generated-code promotion must consume that same semantic
oracle rather than define separate parser behavior.

The external binary-inspection authority for generated artifacts also remains
blocked by `doc/08_tracking/bug/parser_inspection_atomic_input_owner_gap_2026-09-27.md`:
the native inspection V1 start now combines pinned exact-environment execution
with one copied input and a ticket-bound sideband receipt, but the Simple lease,
two-tool compiler owner, and product admission are unfinished. Separate V3 and
V4 receipts still cannot be joined to satisfy EODL REQ-016.
