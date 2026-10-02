# SimpleOS CLI target identity — continuation gate

Baseline: `50d73b7abfb1c8a607ca0c692f825d07fe2ec8e0`.
Owner: item1_astra_impl. Merge owner/reviewer: root.
Requirements: platform unification REQ-001, REQ-011, REQ-016, REQ-022.
Status: source candidate; native SSpec/docgen **UNRUN**.

## Concrete scope and architecture

The platform catalog remains the identity authority. Its CLI projection accepts
only canonical architecture rows (`*-simpleos`), their declared aliases, the
`simpleos-<alias>` CLI spelling, and their canonical userland triple. A small
`Architecture?` result avoids returning the catalog's large optional record.
General build catalog lookup retains its board/host/kernel-triple behavior;
the architecture-only CLI projection rejects those identities.

The required spelling `riscv64-unknown-simpleos` is an explicit catalog alias
of the established RV64GC target. The catalog's ABI and generated-code profile
remain RV64GC; no global target-triple rename occurs in this bounded change.

`arch_from_name` delegates to this registry projection. `os_parse_arch_arg`
preserves explicit CLI selection first, then `SIMPLEOS_QEMU_ARCH`, then actual
host discovery. An unknown result is refused with an actionable diagnostic;
no x86_64 fallback is invented. A Windows host without the current discovery
provider must select `--arch` or configure the environment default explicitly.

## Acceptance and test-before-source record

The focused SSpec was authored before source changes. Executable RED/GREEN was
not observed: root confirmed no qualified runtime. Disk capacity is below the
build guard, so no bootstrap, native build or worktree duplication was started.

| Criterion | Focused scenario |
|---|---|
| Canonical aliases and userland triples choose one registry architecture | x86_64 aliases plus AArch64/RV64 and retained 32-bit targets |
| Invalid, host, bare-metal kernel and physical-board names fail honestly | Registry/architecture nil plus actual CLI inspection refusal |
| Environment defaults retain guest intent | RV64 remains RV64 |
| CLI arguments override environment selection | Inline target and separated architecture flags |
| Unknown discovery and invalid defaults are not silently admitted | Pure discovery facts and actual invalid environment selection |

Resume once with a provenance-admitted runtime and retain executed-assertion
evidence, source identity, output and generated captures:

```text
<runtime> test test/01_unit/os/qemu_target_selection_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/cli_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/simpleos_machine_catalog_projection_spec.spl --mode=interpreter
<runtime> test test/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.spl --mode=interpreter
<runtime> spipe-docgen test/01_unit/os/qemu_target_selection_v1_spec.spl --output doc/06_spec --no-index
<runtime> sspec-maintain scan test/01_unit/os/qemu_target_selection_v1_spec.spl
```

Run lint on the seven changed production files and retain real CLI alias
inspection/run evidence on the prepared Linux/Windows hosts. Existing live
route prerequisites are unchanged. The new unit scenarios and draft manual
do not replace native host, QEMU boot, guest compiler or release qualification.
All selected umbrella and inherited requirements remain active; no completion
percentage or whole-item PASS follows from this fix.

## Remaining source findings retained by this bounded review

The prior `50d73b7abfb` cache-admission/inspection-mode fix remains additive;
this change does not supersede it. Target alias resolution is a source fix,
not completion of the wider product and target matrix in REQ-011.

`src/compiler/10.frontend/core/frontend.spl:117` still records
`candidate_engine_available: false` and zero compared cases, so REQ-003/004
parser qualification remains open. `src/os/cli.spl` still explicitly labels
shell and bootstrap execution unavailable; constructing guest launch values
does not implement REQ-010/016/017 guest workflows. The image CLI still
describes its x86_64 NVFS carrier scope; broader REQ-012/013 image qualification
is not established here. Other selected and inherited rows retain their
existing plan/TODO authority and were not re-certified by this narrow review.
