# feature_tracking_done_gate_spec

> Feature tracking done-gate lint coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# feature_tracking_done_gate_spec

Feature tracking done-gate lint coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feature tracking done-gate lint coverage.

## Scenarios

### feature tracking done gate lint

#### flags done feature rows missing traceability evidence

- flags done feature rows missing traceability evidence
   - Expected: count_feature_tracking_lint(source, "TRK001") equals `1`
   - Expected: count_feature_tracking_lint_with_level(source, "TRK001", LintLevel.Deny) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags done feature rows missing traceability evidence")
val source = feature_tracking_header() +
    "    \"FR-TRACK-001\",core,device,component,\"Done bad\",\"Missing evidence\",done,P1,doc/08_tracking/feature/source.md,none,none,none,none,none,none,none,none,none,none,none,none,none,none,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(1)
expect(count_feature_tracking_lint_with_level(source, "TRK001", LintLevel.Deny)).to_equal(1)
```

</details>

#### flags done feature rows missing unit, integration, and guide evidence

- flags done feature rows missing unit, integration, and guide evidence
   - Expected: count_feature_tracking_lint(source, "TRK001") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags done feature rows missing unit, integration, and guide evidence")
val source = feature_tracking_header() +
    "    \"FR-TRACK-005\",core,device,component,\"Done without tests\",\"Missing final evidence\",done,P1,doc/08_tracking/feature/source.md,doc/02_requirements/feature/good.md,doc/01_research/local/good.md,doc/03_plan/good.md,doc/04_architecture/good.md,doc/05_design/good.md,test/03_system/app/good_spec.spl,doc/06_spec/system/app/good_spec.md,src/app/good/main.spl,none,none,none,github,123,https://example.invalid/123,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(1)
```

</details>

#### accepts done feature rows with complete traceability evidence

- accepts done feature rows with complete traceability evidence
   - Expected: count_feature_tracking_lint(source, "TRK001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts done feature rows with complete traceability evidence")
val source = feature_tracking_header() +
    "    \"FR-TRACK-002\",core,device,component,\"Done good\",\"Complete evidence\",done,P1,doc/08_tracking/feature/source.md,doc/02_requirements/feature/good.md,doc/01_research/local/good.md,doc/03_plan/good.md,doc/04_architecture/good.md,doc/05_design/good.md,test/03_system/app/good_spec.spl,doc/06_spec/system/app/good_spec.md,src/app/good/main.spl,test/01_unit/app/good_spec.spl,test/02_integration/app/good_spec.spl,doc/07_guide/app/good.md,github,123,https://example.invalid/123,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(0)
```

</details>

#### does not require traceability evidence for requested feature rows

- does not require traceability evidence for requested feature rows
   - Expected: count_feature_tracking_lint(source, "TRK001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not require traceability evidence for requested feature rows")
val source = feature_tracking_header() +
    "    \"FR-TRACK-003\",core,device,component,\"Requested\",\"Not complete\",request,P2,doc/08_tracking/feature/source.md,none,none,none,none,none,none,none,none,none,none,none,none,none,none,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(0)
```

</details>

#### ignores invalid done rows

- ignores invalid done rows
   - Expected: count_feature_tracking_lint(source, "TRK001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores invalid done rows")
val source = feature_tracking_header() +
    "    \"FR-TRACK-004\",core,device,component,\"Invalid done\",\"Superseded\",done,P2,doc/08_tracking/feature/source.md,none,none,none,none,none,none,none,none,none,none,none,none,none,none,2026-06-04,2026-06-04,2026-06-04,false\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87af14dc6b712336f08b47ed84a7ac89779be264cd1b1949abd4d06f441f1a75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87af14dc6b712336f08b47ed84a7ac89779be264cd1b1949abd4d06f441f1a75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87af14dc6b712336f08b47ed84a7ac89779be264cd1b1949abd4d06f441f1a75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/feature_tracking_done_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/feature_tracking_done_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/feature_tracking_done_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags done feature rows missing traceability evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags done feature rows missing unit, integration, and guide evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts done feature rows with complete traceability evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
