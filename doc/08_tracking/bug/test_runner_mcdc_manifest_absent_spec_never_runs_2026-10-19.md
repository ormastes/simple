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

When the compile output carries neither manifest marker
(`mcdc_obligation_manifest_absent`), take the existing MC/DC interpreter fallback.
It is tagged `degraded=mcdc-obligation-manifest-absent` and reports the spec's
real pass/fail. A manifest that is present but malformed still fails, and
`--coverage` still fails closed.

## Specs

- Reproducer: `test/01_unit/lib/test_runner_mcdc_manifest_absent_spec.spl`, first
  example. It runs the dir lane over `test/fixtures/test_runner_mcdc/compiles_fixture.spl`.
  It went from `outcome=ERROR` to `outcome=OK passed=1 degraded=mcdc-obligation-manifest-absent`.
- Generalization (same file): only marker-free output counts as absent. BEGIN
  without END, END without BEGIN, and a valid block do not.
