# Minimal Native-Compile Performance Admission

Source:
`test/03_system/app/compiler/feature/compiler_minimal_native_compile_perf_spec.spl`

Manual mirror status: **source-mirrored; executable regeneration TEST_BLOCKED**.
No admitted pure-Simple full CLI was available on 2026-08-16, so this document
does not claim docgen provenance or runtime PASS.

## Purpose

Prove that a minimal native-compile performance result is non-vacuous,
identity-bound, bounded, and compared with an admitted equivalent baseline.

## Audience

Compiler-performance owners and release reviewers who need to reproduce or
reject a minimal native-build timing/RSS claim without seed fallback.

## Preconditions

- The SSpec runner is an admitted pure-Simple self-hosted runtime.
- `SIMPLE_CMNCP_COMPILER` identifies the admitted compiler under measurement.
- `SIMPLE_CMNCP_COMPILER_SHA256` is its exact lowercase SHA-256.
- `SIMPLE_CMNCP_ADMISSION_RECEIPT` is an immutable text receipt containing:

```text
schema=compiler-minimal-native-compile-admission-v1
runtime=pure-simple-self-hosted
runtime_probe=pass
rust_seed_used=false
compiler_path=<exact SIMPLE_CMNCP_COMPILER value>
compiler_sha256=<exact SIMPLE_CMNCP_COMPILER_SHA256 value>
```

- `SIMPLE_CMNCP_WORK_DIR` is an isolated lane directory.
- The three `SIMPLE_CMNCP_BASELINE_*` variables are positive values from the
  identical five-run campaign on the admitted baseline revision.
- `/usr/bin/time` is GNU time.

## Operator workflow and observable steps

1. Admit an exact pure-Simple compiler identity.
2. Reject every Rust-seed provenance path.
3. Bind the admission receipt to path and SHA-256.
4. Require a successful native-build result.
5. Require a nontrivial emitted executable.
6. Execute and hash the emitted artifact.
7. Require a positive admitted baseline.
8. Apply the 120 percent time and 110 percent RSS ceilings.
9. Accept measurements exactly on every budget boundary.
10. Reject a campaign that is not exactly five samples.
11. Reject an unavailable compiler without fallback.
12. Load the qualified compiler receipt and baseline.
13. Compile and execute the minimal fixture five times.
14. Verify timing, RSS, artifact, and regression evidence.

## Results

The deterministic scenarios assert stable admission reasons. The live scenario
requires `status=pass`, `reason=within-budget`, five samples, positive p50/p95
and RSS, and a 64-character artifact hash. There is no skip or placeholder
branch. Missing qualification therefore produces a visible failing assertion.
The campaign writes the complete identity, baseline, measurement, threshold,
and artifact tuple to
`$SIMPLE_CMNCP_WORK_DIR/minimal-native-compile-perf.receipt`; failure to write
that retained evidence changes the result to `fail`.

## Scenario narratives

The first three scenarios protect compiler admission, the next three protect
artifact admission, and the next three protect the regression budget. Two
preflight scenarios prove unavailable/invalid campaigns block before effects.
The final scenario is the only live measurement and runs exactly once.

## Requirement map

| Requirement | Evidence |
|---|---|
| REQ-CMNCP-001 | identity, seed, receipt scenarios |
| REQ-CMNCP-002 | compile and artifact scenarios |
| REQ-CMNCP-003 | baseline and ceiling scenarios |
| REQ-CMNCP-004 | invalid-count block, missing-compiler block, one live campaign |
| NFR-CMNCP-001 | bound compiler, fixture, baseline, and artifact identity |
| NFR-CMNCP-002 | fixed sample count and bounded child processes |
| NFR-CMNCP-003 | fail-closed prerequisite and evidence outcomes |

## Static scorecard

| Component | Prepared status |
|---|---|
| Step-based workflow | complete; 14 visible steps |
| Real assertions | complete; no placeholder pass branch |
| REQ traceability | complete; three scenarios per REQ |
| Mirrored path/manual | complete and source-mirrored |
| Runtime/docgen provenance | TEST_BLOCKED |

This is a source-review scorecard, not `sspec-maintain` machine output.

## Findings and remediation

The only open finding is the unavailable admitted full CLI. Produce a qualified
runtime and admission/baseline tuple, then run the single command from the test
plan. Any nonzero exit, missing receipt, bad artifact, or exceeded budget stays
failed; do not edit the manual to bypass it.

## Evidence and provenance

The executable source, requirements, implementation, plan, feature-expert
entry, and LLM wiki use the `compiler_minimal_native_compile_perf` slug. A live
run must retain the admission receipt, SSpec output, and
`minimal-native-compile-perf.receipt`. No runtime-generated evidence currently
exists.

## Compatibility and current limitations

The qualified live command remains `TEST_BLOCKED`. The historical Rust seed is
explicitly inadmissible, and the available Stage2-only candidate cannot run
SSpec or compile the fixture successfully. No measured baseline is recorded by
this manual.
