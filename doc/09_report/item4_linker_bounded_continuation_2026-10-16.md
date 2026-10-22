# Item 4 linker continuation: blocked acceptance

Date: 2026-10-16. Inspected target: `release_phase3` at
`1e93dca4ce3d7be2187da1b67cfeb1180179682e`.
STATUS: BLOCKED. This report does not certify implementation or Phase3 PASS.

## Scope and isolation

Fresh bounded continuation of session `01a0ffa4-11b8-7133-9bab-a82331e7d675`;
the old rollout was not resumed. Item 4 remains the scope defined in
[the seven-item plan](../03_plan/seven_plans_host_completion_2026-09-29.md#4-simple-linker-mold-based-mdsoc-architecture-and-implementation-plan).
No requirements were removed or host support inferred from another object format.

PR [3072](https://github.com/ormastes/simple/pull/3072) is MERGED into
`release_phase3` (2026-10-12); its head was
`work/item6-release-phase3-20261011`. It is not Item 4 acceptance evidence.

The shared `C:/dev/simple` checkout had 398 dirty entries, including linker,
compiler, runtime and bootstrap files. They were preserved. Authorship and
landing of this report use isolated branch `work/item4-bounded-audit-20261016`
in `C:/dev/simple-item4-bounded-20261016`. Sidecars: N/A; narrow evidence audit.
Merge owner and final reviewer: this continuation.

Process inspection found concurrent Item 2 and Item 7 Codex processes and a
Phase3 archive-enum materialization process. Existing Phase3 evidence lives at
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016`. No compiler build,
cache mutation, process termination or change to another lane was performed.

## Concrete remaining blockers

| Gate | Observed evidence | Required next action / owner |
|---|---|---|
| Generator nonzero addresses | `src/app/linker_gen/main.spl` still uses integer-to-character conversion in `format_hex`; the open bug and system spec explicitly retain a nonzero-input failure | Item 4: repair using supported text operations and run the actual nonzero-address regression with an admitted runtime |
| Generator section type | `parser.spl` exposes `Section.section_type` and `is_nobits()`, but `generate_section` does not consume either | Item 4: define and test the retained NOBITS/NOLOAD contract before claiming generator completion |
| Executable system checks | No deployed runtime was found under the inspected shared checkout's `bin/release`; the active launcher's A174 producer is Stage 2 | Bootstrap owner: supply a hash/provenance-bound runtime admitted for general SPipe and docgen; Stage 2 compiler evidence cannot replace this |
| Phase3 compiler | Existing `cycle2-driver-cuda-hir-triage.md` records unresolved `native_capsule_function_metadata_identity_v1` / `native_capsule_type_def_identity_v1` in `driver_types.spl`, and unresolved MIR types in `cuda_backend_port.spl` | Active Phase3 owner: repair and retain a terminal, source-bound result; this lane must not launch a duplicate build |
| Full Item 4 acceptance | No new executable/compiler-corpus, host-parity, paired fast/bounded digest, resource-accounting or boot evidence was produced here | Item 4 and host owners: satisfy the retained linker plan gates; do not change the completion predicate based on this audit |

References: [generator bug](../08_tracking/bug/linker_gen_format_hex_nonzero_garbage_2026-09-06.md),
[retained design](../05_design/compiler/linker/mold_mdsocpp_linker_design.md),
[retained execution plan](../03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md),
and executable `test/03_system/feature/app/linker_gen_spec.spl`.

## Verification boundary

Read-only source and process inspection only; zero executable acceptance checks
and zero verify/fix cycles. No Stage 2 run is represented as a Stage 4 result.
No implementation changes, completion flags, host certification, release tags
or publication are authorized by this report. Landing this report closes only
the evidence audit, not Item 4. Resume implementation after the runtime/build
ownership blockers above are resolved, preserving the original failure logs.
