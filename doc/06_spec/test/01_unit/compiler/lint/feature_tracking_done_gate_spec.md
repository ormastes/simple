# feature_tracking_done_gate_spec

> Feature tracking done-gate lint coverage.

<!-- sdn-diagram:id=feature_tracking_done_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_tracking_done_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_tracking_done_gate_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_tracking_done_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Feature tracking done-gate lint coverage.

## Scenarios

### feature tracking done gate lint
_Verifies traceability enforcement for canonical feature_db.sdn rows._

#### flags done feature rows missing traceability evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_tracking_header() +
    "    \"FR-TRACK-001\",core,device,component,\"Done bad\",\"Missing evidence\",done,P1,doc/08_tracking/feature/source.md,none,none,none,none,none,none,none,none,none,none,none,none,none,none,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(1)
expect(count_feature_tracking_lint_with_level(source, "TRK001", LintLevel.Deny)).to_equal(1)
```

</details>

#### flags done feature rows missing unit, integration, and guide evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_tracking_header() +
    "    \"FR-TRACK-005\",core,device,component,\"Done without tests\",\"Missing final evidence\",done,P1,doc/08_tracking/feature/source.md,doc/02_requirements/feature/good.md,doc/01_research/local/good.md,doc/03_plan/good.md,doc/04_architecture/good.md,doc/05_design/good.md,test/03_system/app/good_spec.spl,doc/06_spec/system/app/good_spec.md,src/app/good/main.spl,none,none,none,github,123,https://example.invalid/123,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(1)
```

</details>

#### accepts done feature rows with complete traceability evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_tracking_header() +
    "    \"FR-TRACK-002\",core,device,component,\"Done good\",\"Complete evidence\",done,P1,doc/08_tracking/feature/source.md,doc/02_requirements/feature/good.md,doc/01_research/local/good.md,doc/03_plan/good.md,doc/04_architecture/good.md,doc/05_design/good.md,test/03_system/app/good_spec.spl,doc/06_spec/system/app/good_spec.md,src/app/good/main.spl,test/01_unit/app/good_spec.spl,test/02_integration/app/good_spec.spl,doc/07_guide/app/good.md,github,123,https://example.invalid/123,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(0)
```

</details>

#### does not require traceability evidence for requested feature rows

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_tracking_header() +
    "    \"FR-TRACK-003\",core,device,component,\"Requested\",\"Not complete\",request,P2,doc/08_tracking/feature/source.md,none,none,none,none,none,none,none,none,none,none,none,none,none,none,2026-06-04,2026-06-04,2026-06-04,true\n"

expect(count_feature_tracking_lint(source, "TRK001")).to_equal(0)
```

</details>

#### ignores invalid done rows

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
