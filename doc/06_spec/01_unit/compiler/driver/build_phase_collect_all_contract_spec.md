# A build phase must reach the end of its work list

> This is the CLASS spec, not the instance one. The instance defect was

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# A build phase must reach the end of its work list

This is the CLASS spec, not the instance one. The instance defect was

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / driver |
| Status | Similar-problem detection guard (class-level) |
| Source | `test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

This is the CLASS spec, not the instance one. The instance defect was
`driver_aot_native_output.spl` returning on the first bad module. The class is
broader and has recurred in at least three places in this repo:

> **a phase that abandons the remaining work on the first failure.**

`driver_source_pipeline_parsing.spl` did it across 619 files. The native output
path did it across modules. Any future phase — lowering, linking, spec discovery
— can do it again, and the symptom is always the same and always misread: the
build reports *one* problem, the engineer fixes it, and pays another full run to
discover the second. Each occurrence costs a ~20-minute bootstrap cycle per
defect instead of one cycle for all of them.

The audience is anyone writing a loop over units of work inside a build phase.

## Scope and Preconditions

This spec does not test one call site. It pins the *contract* that any
collect-all phase must satisfy, exercised through the shared vocabulary in
`compiler.driver.driver_build.build_outcome`:

1. **Completeness** — the number of recorded outcomes equals the number of units
   in the work list, even when the first unit fails. An outcome set smaller than
   the work list is the signature of an abandoned phase.
2. **No early exit on the first failure** — a failure at index 0 must not stop
   the loop; later failures must still be named.
3. **Fail closed at the boundary, not early** — the verdict is computed after the
   loop, and it is non-empty whenever any unit is non-OK.
4. **No fabricated artifacts** — a failed unit contributes nothing to the
   artifact list. Cf. `linker/native_binary/stubs.rs:209-221`, where fabricated
   zero-returning stubs masked missing symbols.

## Expected Outcome

The simulated phase below fails its FIRST unit and still attempts all five,
records five outcomes, names both failing units, produces exactly three
artifacts, and fails closed only after the loop has finished.

## Scenarios

### a build phase reaches the end of its work list

#### records one outcome per unit even when the first unit fails

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records one outcome per unit even when the first unit fails
   - Expected: outcomes.len() equals `paths.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records one outcome per unit even when the first unit fails")
val paths = five_unit_paths()
val (outcomes, _artifacts) = simulated_phase(paths,
    ["fixture/a_broken.spl", "fixture/d_broken.spl"])
# An outcome set smaller than the work list is the signature of a phase
# that abandoned its remaining work.
expect(outcomes.len()).to_equal(paths.len())
```

</details>

#### names a failure that occurs AFTER the first failure

- names a failure that occurs AFTER the first failure
   - Expected: errors.len() equals `2`
   - Expected: errors[0] equals `fixture/a_broken.spl`
   - Expected: errors[1] equals `fixture/d_broken.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names a failure that occurs AFTER the first failure")
val (outcomes, _artifacts) = simulated_phase(five_unit_paths(),
    ["fixture/a_broken.spl", "fixture/d_broken.spl"])
val errors = outcomes.paths_in(BuildOutcomeKind.ERROR)
expect(errors.len()).to_equal(2)
expect(errors[0]).to_equal("fixture/a_broken.spl")
expect(errors[1]).to_equal("fixture/d_broken.spl")
```

</details>

#### leaves no unit unaccounted for

- leaves no unit unaccounted for
   - Expected: outcomes.has_path(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves no unit unaccounted for")
val (outcomes, _artifacts) = simulated_phase(five_unit_paths(),
    ["fixture/a_broken.spl", "fixture/d_broken.spl"])
for path in five_unit_paths():
    expect(outcomes.has_path(path)).to_equal(true)
```

</details>

### a build phase fails closed at the boundary, not early

#### produces a non-empty verdict naming every failing unit

- produces a non-empty verdict naming every failing unit
   - Expected: outcomes.all_ok() is false
   - Expected: verdict contains `fixture/a_broken.spl`
   - Expected: verdict contains `fixture/d_broken.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces a non-empty verdict naming every failing unit")
val (outcomes, _artifacts) = simulated_phase(five_unit_paths(),
    ["fixture/a_broken.spl", "fixture/d_broken.spl"])
expect(outcomes.all_ok()).to_equal(false)
val verdict = outcomes.verdict()
expect(verdict.contains("fixture/a_broken.spl")).to_equal(true)
expect(verdict.contains("fixture/d_broken.spl")).to_equal(true)
```

</details>

#### never fabricates an artifact for a failed unit

- never fabricates an artifact for a failed unit
   - Expected: artifacts.len() equals `3`
   - Expected: outcomes.ok_count() equals `3`
   - Expected: artifact does not contain `broken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never fabricates an artifact for a failed unit")
val (outcomes, artifacts) = simulated_phase(five_unit_paths(),
    ["fixture/a_broken.spl", "fixture/d_broken.spl"])
# Three clean units, three artifacts. Never five.
expect(artifacts.len()).to_equal(3)
expect(outcomes.ok_count()).to_equal(3)
for artifact in artifacts:
    expect(artifact.contains("broken")).to_equal(false)
```

</details>

#### still succeeds cleanly when nothing is broken

- still succeeds cleanly when nothing is broken
   - Expected: outcomes.all_ok() is true
   - Expected: outcomes.verdict() equals ``
   - Expected: artifacts.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still succeeds cleanly when nothing is broken")
val (outcomes, artifacts) = simulated_phase(five_unit_paths(), [])
expect(outcomes.all_ok()).to_equal(true)
expect(outcomes.verdict()).to_equal("")
expect(artifacts.len()).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-DRIVER-BUILD-OUTCOME-002`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4169f8c7b79bb8d4452c3fe5e68d6b89451ba06cc52997c3851b36d4d9b22a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4169f8c7b79bb8d4452c3fe5e68d6b89451ba06cc52997c3851b36d4d9b22a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4169f8c7b79bb8d4452c3fe5e68d6b89451ba06cc52997c3851b36d4d9b22a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/build_phase_collect_all_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/build_phase_collect_all_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/build_phase_collect_all_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records one outcome per unit even when the first unit fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names a failure that occurs AFTER the first failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves no unit unaccounted for' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
