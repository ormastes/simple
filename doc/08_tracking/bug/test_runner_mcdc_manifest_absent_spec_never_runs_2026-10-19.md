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

## Follow-up: asserted fallback did not transport BDD evidence (2026-10-27)

The directory regression passed without `--assert-ran`, but a fresh probe with
`SIMPLE_MCDC_MANIFEST_ABSENT=degrade` and `--assert-ran` still failed with
`--assert-ran: structured BDD evidence is unavailable for this execution mode`.
The MC/DC fallback launched `run <original-file>` and fed its stdout to
`make_result_from_output`. That mapper intentionally rejects stdout summaries
when assertion evidence is required. The normal interpreter path already had
the canonical transport: set `SIMPLE_TEST_RESULT_FILE`, pass
`--test-result-file=<path>`, parse the `simple-bdd-v1` evidence with
`make_result_from_structured_evidence`, then remove both the result and
expectations files. The fallback skipped that transport, so the explicitly
permitted degrade could not satisfy the same `--assert-ran` contract.

The source candidate now shares the interpreter child evidence transport and
result parser between the normal interpreter path and the MC/DC fallback. The
fallback still runs the original file and retains its MC/DC skip/degrade tags.
The manifest-absent spec now covers asserted green, red, and zero-example
outcomes, including each directory child's exit status. A validated red BDD
count keeps the bounded assertion diagnostic under an explicit authenticated
failure marker. A validated zero/zero result maps to the unrun verdict shape
with `executed=0`, `failed=1`, `dropped=1`, and `reason=zero-examples`; absent
evidence remains a distinct `bdd-evidence-unavailable` result. A nonzero child
exit after an authenticated pass preserves its real pass count and emits an
ERROR verdict with `failed=0` and `process_error=1`.

The single-file runner now requests the same unique `simple-bdd-v1` evidence
for every child run. Valid structured counts take precedence over stdout glyphs;
glyph counting remains a fallback only when no valid receipt exists. This
prevents a nested red child transcript printed by an outer failing example
from increasing the outer failure count. On the pinned 2026-10-27 seed, the
focused parser and protocol specs passed 3/3 and 7/7. The single-file evidence
control passed 8/8, including an actual nested red transcript that reported
`Results: 6 total, 5 passed, 1 failed`, lone and mixed orphan examples, a
zero-example failure, and a post-pass process failure with `Passed: 1` and
`Failed: 0`. Source pins were unchanged. Its logs are under
`build/phase1-spipe-calibration-20261027/fresh-seed-81e9a8-single-evidence-afterreview-03/`.
The first seven-case run was 5/7 because the nested fixture had a malformed
function return-type token and the zero-example assertion omitted the runner's
actual `no examples executed` wording. Both test-only issues were corrected;
the final eight-case run passed 8/8.

The manifest-fallback integration spec still reaches a generic
`smf-compile-error` fallback first (`i64` has no field `recorder`), so the
successful-compile/manifest-absent branch was not exercised. The one run after
updating its reason assertions passed 5/6 examples; its only failure was a
stale expected diagnostic substring (`expected 2 to_equal 3`; authenticated
output says `expected 2 to equal 3`). That expected string is corrected, but
the integration spec has not been rerun since. The successful-compile
manifest-absent branch remains **UNQUALIFIED**; no pass claim is made for it.
