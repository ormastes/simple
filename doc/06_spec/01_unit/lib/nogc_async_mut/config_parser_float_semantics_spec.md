# config_parser_float_semantics_spec

> Verifies the config parser float semantics behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# config_parser_float_semantics_spec

Verifies the config parser float semantics behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/config_parser_float_semantics_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the config parser float semantics behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### nogc_async_mut config float semantics

#### parses valid decimal, negative, and exponent values

- Verify: parses valid decimal, negative, and exponent values
   - Expected: get_config_float(section, "valid", 9.5) equals `1.25`
   - Expected: get_config_float(section, "negative", 9.5) equals `-2.5`
   - Expected: get_config_float(section, "exponent", 9.5) equals `625.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_ASYNC_MUT_CONFIG_PARSER-001
step("Verify: parses valid decimal, negative, and exponent values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(get_config_float(section, "valid", 9.5)).to_equal(1.25)
expect(get_config_float(section, "negative", 9.5)).to_equal(-2.5)
expect(get_config_float(section, "exponent", 9.5)).to_equal(625.0)
```

</details>

#### defaults missing, empty, and malformed values

- Verify: defaults missing, empty, and malformed values
   - Expected: get_config_float(section, "missing", 9.5) equals `9.5`
   - Expected: get_config_float(section, "empty", 9.5) equals `9.5`
   - Expected: get_config_float(section, "malformed", 9.5) equals `9.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_ASYNC_MUT_CONFIG_PARSER-001
step("Verify: defaults missing, empty, and malformed values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(get_config_float(section, "missing", 9.5)).to_equal(9.5)
expect(get_config_float(section, "empty", 9.5)).to_equal(9.5)
expect(get_config_float(section, "malformed", 9.5)).to_equal(9.5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d393c20eb1104ea7ec7544afa2ac2ab8f2c3d3531bd600caeb8b34e9af4454e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d393c20eb1104ea7ec7544afa2ac2ab8f2c3d3531bd600caeb8b34e9af4454e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d393c20eb1104ea7ec7544afa2ac2ab8f2c3d3531bd600caeb8b34e9af4454e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/config_parser_float_semantics_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/config_parser_float_semantics_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/config_parser_float_semantics_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_async_mut/config_parser_float_semantics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/config_parser_float_semantics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/config_parser_float_semantics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
