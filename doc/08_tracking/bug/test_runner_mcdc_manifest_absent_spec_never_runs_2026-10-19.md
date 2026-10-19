# Specs that compile standalone under the seed never run: "missing or malformed MC/DC obligation manifest"

- Status: fixed (branch `work/test-runner-whole-suite`)
- Found: 2026-10-19, first whole-suite sweep on `59d84defe67`. 24 of the first 51 FAILs were this error.

## Defect

With MC/DC on (the default), the runner compiles each spec standalone. When that
compile succeeds, the runner requires the compiler's MC/DC obligation manifest
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`, the `mcdc_enabled`
block after the compile). Only the pure-Simple compiler driver produces that
manifest (`src/compiler/10.frontend/core/ast_coverage_inventory.spl`). The Rust
seed's `compile` exits 0, writes the SMF, and prints no marker. As a result every
spec that compiles cleanly under the seed failed in about 80 ms without running an
example. Specs whose compile *failed* were degraded to the interpreter and did run,
so the gate was backwards for the seed lane.

## Fix

When the compile output has neither manifest marker (`mcdc_obligation_manifest_absent`), the runner
still fails closed by default. Under the pure-Simple compiler, which reads `SIMPLE_MCDC_MODE`,
an absent manifest is a compiler regression, and silently degrading it would bypass the
signed-waiver rule of `resolve_mcdc_mode_for_profile`. The default error now names the cause:
`missing MC/DC obligation manifest (compiler emitted none; ...)`.

A toolchain that cannot produce the manifest, such as the Rust seed sweep, opts in with
`SIMPLE_MCDC_MANIFEST_ABSENT=degrade`. `mcdc_manifest_absent_degrade_opted_in` accepts
only that exact value, following the `SIMPLE_COVERAGE_FALLBACK=interpreter` precedent.
The spec then takes the existing MC/DC interpreter fallback, tagged
`degraded=mcdc-obligation-manifest-absent`, and reports its real pass/fail.
A manifest that is present but malformed still fails, and `--coverage` still fails
closed. The app copy `src/app/test_runner_new/test_runner_execute.spl` has no
manifest gate (it is unreached), so it needs no change.

## Specs

- Reproducer: `test/01_unit/lib/test_runner_mcdc_manifest_absent_spec.spl`, opt-in
  example. It runs the dir lane over `test/fixtures/test_runner_mcdc/compiles_fixture.spl` with
  the opt-in. It went from `outcome=ERROR` to `outcome=OK passed=1`, and the
  `degraded=` token is required whenever `[mcdc-fallback]` appears.
- Fail-closed (same file): with the policy unset the lane never degrades. If the
  compiler emitted no manifest the verdict is `outcome=ERROR`.
- Generalization (same file): only marker-free output counts as absent, and only
  `"degrade"` counts as the opt-in.
