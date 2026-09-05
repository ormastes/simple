# backend_layer_artifact_matrix_spec

> Backend layer artifact matrix acceptance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_layer_artifact_matrix_spec

Backend layer artifact matrix acceptance.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Backend layer artifact matrix acceptance.

This spec executes the repository's real CPU and GPU artifact checkers, then
accounts for their evidence against the canonical ten-stage contract. The
current origin has no shared canonical BackendIR, Object, LinkedBinary, or
RunReadbackReceipt publication hooks, so those required cells must remain FAIL.
Independent checker artifacts are supporting evidence and never promote a
missing canonical hook to PASS, SKIP_UNAVAILABLE, or NOT_APPLICABLE.

## Scenarios

### Backend layer artifact and runtime matrix

#### should account for every available checker row and fail closed on missing canonical hooks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should account for every available checker row and fail closed on missing canonical hooks
- select all compiler artifact stages
   - Expected: file_exists(fixture.cpu_checker) is true
   - Expected: file_exists(fixture.gpu_checker) is true
   - Expected: file_exists(fixture.compiler_fixture) is true
- compile the layered backend fixture
- validate every emitted compiler layer
   - Expected: shared.status equals `FAIL`
   - Expected: shared.reason equals `canonical-shared-stage-hooks-absent`
   - Expected: shared.accounted equals `0`
   - Expected: shared.missing_required equals `6`
   - Expected: backend.status equals `FAIL`
   - Expected: backend.reason equals `required-canonical-backend-hooks-absent`
   - Expected: backend.accounted equals `backend.expected`
   - Expected: backend.expected equals `expected_checker_rows`
   - Expected: backend.invalid_skips equals `0`
- execute the deepest available backend layer
   - Expected: runtime.status equals `FAIL`
   - Expected: runtime.reason equals `canonical-run-readback-receipt-hook-absent`
   - Expected: runtime.accounted equals `runtime.expected`
   - Expected: runtime.invalid_skips equals `0`
   - Expected: runtime.missing_required equals `1`
- account for the complete backend environment matrix
   - Expected: ledger.status equals `FAIL`
   - Expected: ledger.reason equals `canonical-ten-stage-ledger-absent`
   - Expected: ledger.accounted equals `ledger.expected`
   - Expected: ledger.expected equals `expected_checker_rows`
   - Expected: ledger.missing_required equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should account for every available checker row and fail closed on missing canonical hooks")
step("select all compiler artifact stages")
val fixture = prepare_backend_artifact_fixture()
expect(file_exists(fixture.cpu_checker)).to_equal(true)
expect(file_exists(fixture.gpu_checker)).to_equal(true)
expect(file_exists(fixture.compiler_fixture)).to_equal(true)

step("compile the layered backend fixture")
val compilation = compile_backend_artifact_fixture(fixture)
expect(compilation.cpu_exit).to_be_less_than(2)
expect(compilation.gpu_exit).to_be_less_than(2)
expect_not(compilation.cpu_stdout.contains("status=UNKNOWN"))
expect_not(compilation.gpu_stdout.contains("_result=UNKNOWN"))

step("validate every emitted compiler layer")
val shared = check_shared_stage_artifacts(compilation)
val backend = check_backend_stage_artifacts(compilation)
expect(shared.status).to_equal("FAIL")
expect(shared.reason).to_equal("canonical-shared-stage-hooks-absent")
expect(shared.accounted).to_equal(0)
expect(shared.missing_required).to_equal(6)
expect(backend.status).to_equal("FAIL")
expect(backend.reason).to_equal("required-canonical-backend-hooks-absent")
expect(backend.accounted).to_equal(backend.expected)
val expected_checker_rows = fixture.expected_cpu_rows + fixture.expected_gpu_rows
expect(backend.expected).to_equal(expected_checker_rows)
expect(backend.invalid_skips).to_equal(0)
expect(backend.missing_required).to_be_greater_than(3)

step("execute the deepest available backend layer")
val runtime = check_runtime_readback_receipt(compilation)
expect(runtime.status).to_equal("FAIL")
expect(runtime.reason).to_equal("canonical-run-readback-receipt-hook-absent")
expect(runtime.accounted).to_equal(runtime.expected)
expect(runtime.invalid_skips).to_equal(0)
expect(runtime.missing_required).to_equal(1)

step("account for the complete backend environment matrix")
val ledger = check_complete_matrix_ledger(compilation)
expect(ledger.status).to_equal("FAIL")
expect(ledger.reason).to_equal("canonical-ten-stage-ledger-absent")
expect(ledger.accounted).to_equal(ledger.expected)
expect(ledger.expected).to_equal(expected_checker_rows)
expect(ledger.missing_required).to_equal(1)
expect(compilation.cpu_stdout).to_contain("cpu_backend_matrix status=")
expect(compilation.gpu_stdout).to_contain("gpu_backend_matrix status=")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-008`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f61cc7f648a9950286458600e7df449f970977ac5507121e8f517b3001d6e187`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f61cc7f648a9950286458600e7df449f970977ac5507121e8f517b3001d6e187`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f61cc7f648a9950286458600e7df449f970977ac5507121e8f517b3001d6e187`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl
mirror: doc/06_spec/03_system/compiler/backend/backend_layer_artifact_matrix_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/compiler/backend/backend_layer_artifact_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/backend/backend_layer_artifact_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl:208:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should account for every available checker row and fail closed on missing canonical hooks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should account for every available checker row and fail closed on missing canonical hooks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
