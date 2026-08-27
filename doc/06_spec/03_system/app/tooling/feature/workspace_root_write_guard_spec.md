# Workspace Root Write Guard (behavioral)

> Executes the real guard end to end via subprocess. `audit --staged --dry-run`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Workspace Root Write Guard (behavioral)

Executes the real guard end to end via subprocess. `audit --staged --dry-run`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/tooling/feature/workspace_root_write_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executes the real guard end to end via subprocess. `audit --staged --dry-run`
on a clean staged set must exit 0 and print the OK verdict; `audit --strict
--dry-run` over the working tree must exit non-zero and name its violations.
No repo files are mutated: every run uses --dry-run.

## Scenarios

### Workspace root write guard

#### passes a clean staged audit with exit 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- run the guard in staged audit mode over a clean staged set
   - Expected: code equals `0`
   - Expected: output contains `workspace-root-guard: OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the guard in staged audit mode over a clean staged set")
# evidence(protocol_json): exit status and verdict line asserted below are the complete typed oracle
val (code, output) = _guard(["audit", "--staged", "--dry-run"])
expect(code).to_equal(0)  # oracle: a clean staged set must pass with exit 0
expect(output.contains("workspace-root-guard: OK")).to_equal(true)
```

</details>

#### fails a strict tree audit with a non-zero exit and a violation count

- run the guard in strict audit mode over the working tree
   - Expected: code != 0 is true
   - Expected: output contains `workspace-root-guard: FAILED with`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the guard in strict audit mode over the working tree")
# evidence(protocol_json): exit status and FAILED verdict asserted below are the complete typed oracle
val (code, output) = _guard(["audit", "--strict", "--dry-run"])
expect(code != 0).to_equal(true)  # oracle: real violations must fail the audit
expect(output.contains("workspace-root-guard: FAILED with")).to_equal(true)
```

</details>

#### reports a diagnostic code per violation family

- run a strict audit and inspect the emitted diagnostic codes
   - Expected: code != 0 is true
   - Expected: output contains `WRG0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run a strict audit and inspect the emitted diagnostic codes")
# evidence(protocol_json): WRG diagnostic codes in output asserted below are the complete typed oracle
val (code, output) = _guard(["audit", "--strict", "--dry-run"])
expect(code != 0).to_equal(true)
expect(output.contains("WRG0")).to_equal(true)  # oracle: violations are reported with WRGxxx diagnostic codes
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8187e64e4f488d6a78194945a894918798a26e8b32afdb12b364a8971408ac4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8187e64e4f488d6a78194945a894918798a26e8b32afdb12b364a8971408ac4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8187e64e4f488d6a78194945a894918798a26e8b32afdb12b364a8971408ac4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/tooling/feature/workspace_root_write_guard_spec.spl
mirror: doc/06_spec/03_system/app/tooling/feature/workspace_root_write_guard_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/tooling/feature/workspace_root_write_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/tooling/feature/workspace_root_write_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
