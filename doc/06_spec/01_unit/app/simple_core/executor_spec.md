# executor_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# executor_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_core/executor_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/app/simple_core/executor_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### generic simple-core SCI command execution

#### keeps recovery help static without provider activation

- Verify: keeps recovery help static without provider activation
   - Expected: result.status equals `SIMPLE_CORE_EXECUTION_OK`
   - Expected: result.route_kind equals `SIMPLE_CORE_ROUTE_CORE`
   - Expected: result.pin_released is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps recovery help static without provider activation")
val result = simple_core_execute_v1(["--help"], _config(), "1.0.0", 1, 4)
expect(result.status).to_equal(SIMPLE_CORE_EXECUTION_OK)
expect(result.route_kind).to_equal(SIMPLE_CORE_ROUTE_CORE)
expect(result.output).to_contain("simple-core commands")
expect(result.pin_released).to_equal(false)
```

</details>

#### routes a generic SCI command and fails closed for its missing locked artifact

- Verify: routes a generic SCI command and fails closed for its missing locked artifact
   - Expected: result.status equals `SIMPLE_CORE_EXECUTION_PROVIDER_FAILED`
   - Expected: result.route_kind equals `SIMPLE_CORE_ROUTE_PROVIDER`
   - Expected: result.provider_status equals `SIMPLE_CORE_PROVIDER_DISPATCH_ADMISSION_FAILED`
   - Expected: result.pin_released is false
   - Expected: result.session_closed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: routes a generic SCI command and fails closed for its missing locked artifact")
val result = simple_core_execute_v1(["format", "file.spl"], _config(), "1.0.0", 1, 4)
expect(result.status).to_equal(SIMPLE_CORE_EXECUTION_PROVIDER_FAILED)
expect(result.route_kind).to_equal(SIMPLE_CORE_ROUTE_PROVIDER)
expect(result.provider_status).to_equal(SIMPLE_CORE_PROVIDER_DISPATCH_ADMISSION_FAILED)
expect(result.diagnostic).to_contain("artifact-missing")
expect(result.pin_released).to_equal(false)
expect(result.session_closed).to_equal(false)
```

</details>

#### rejects an unknown SCI command without probing a provider path

- Verify: rejects an unknown SCI command without probing a provider path
   - Expected: result.status equals `SIMPLE_CORE_EXECUTION_ROUTE_REJECTED`
   - Expected: result.provider_status equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: rejects an unknown SCI command without probing a provider path")
val result = simple_core_execute_v1(["unknown", "file.spl"], _config(), "1.0.0", 1, 4)
expect(result.status).to_equal(SIMPLE_CORE_EXECUTION_ROUTE_REJECTED)
expect(result.diagnostic).to_contain("CLI_COMMAND_UNKNOWN")
expect(result.provider_status).to_equal(-1)
```

</details>

#### keeps an authored provider dispatch unexecuted when routing rejects

- Verify: keeps an authored provider dispatch unexecuted when routing rejects
   - Expected: result.status equals `SIMPLE_CORE_EXECUTION_ROUTE_REJECTED`
   - Expected: result.provider_status equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The executor must not turn an unknown command into a loader probe;
# this is the dispatch boundary for corruption/config rejection paths.
val invalid = CompositionReadResultV1(
    ok: false,
    image: _config().image,
    diagnostic: composition_diagnostic_v1("SCI_CLI_OPTION_ROUTE_SECTION", "cli-option-route", "corrupt"),
)
val result = simple_core_execute_v1(["fmt", "--xformat-mode=check"], invalid, "1.0.0", 1, 4)
expect(result.status).to_equal(SIMPLE_CORE_EXECUTION_ROUTE_REJECTED)
expect(result.provider_status).to_equal(-1)
expect(result.diagnostic).to_contain("SCI_CLI_OPTION_ROUTE_SECTION")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `757a9f83a025c15223a9b9abdece3e102016ffe61d2cc7197687cb5c6b70e83f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `757a9f83a025c15223a9b9abdece3e102016ffe61d2cc7197687cb5c6b70e83f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `757a9f83a025c15223a9b9abdece3e102016ffe61d2cc7197687cb5c6b70e83f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/simple_core/executor_spec.spl
mirror: doc/06_spec/01_unit/app/simple_core/executor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/simple_core/executor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_core/executor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_core/executor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/simple_core/executor_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps recovery help static without provider activation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_core/executor_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a generic SCI command and fails closed for its missing locked artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_core/executor_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown SCI command without probing a provider path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
