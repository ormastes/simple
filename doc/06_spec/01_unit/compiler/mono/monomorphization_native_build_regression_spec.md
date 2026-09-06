# Monomorphization Native Build Regression Specification

> Tests covering monomorphization native-build regression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Monomorphization Native Build Regression Specification

## Scenarios

### monomorphization native-build regression

#### scans block and field expressions without rt_enum_discriminant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scans block and field expressions without rt_enum_discriminant
   - Expected: output.len() equals `1`
   - Expected: stats.generic_functions_found equals `1`
   - Expected: stats.call_sites_found equals `0`
   - Expected: stats.specializations_created equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("scans block and field expressions without rt_enum_discriminant")
val input = module_with_generic_function()
val (output, stats) = run_monomorphization({"mono.regression": input})

expect(output.len()).to_equal(1)
expect(stats.generic_functions_found).to_equal(1)
# Since the worklist fixed point landed (plan 9.3 step 3, 2026-08-21)
# only NON-generic roots and emitted specializations are walked; a
# template body is never scanned on its own, so the self-call inside
# this instantiation-free template is not a call site. The module
# must still come back intact (1 module, 1 template found).
expect(stats.call_sites_found).to_equal(0)
expect(stats.specializations_created).to_equal(0)
```

</details>

#### keeps direct mono compiles off root std.sdn and relative HIR imports

- keeps direct mono compiles off root std.sdn and relative HIR imports
   - Expected: cache_source does not contain `use std.sdn.`
   - Expected: hot_reload_source does not contain `use std.sdn.`
   - Expected: engine_source does not contain `use hir_types.*`
   - Expected: engine_source does not contain `use hir_definitions.*`
   - Expected: integration_source does not contain `for (k, v) in modules`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps direct mono compiles off root std.sdn and relative HIR imports")
val cache_source = rt_file_read_text("src/compiler/40.mono/monomorphize/cache.spl") ?? ""
val hot_reload_source = rt_file_read_text("src/compiler/40.mono/monomorphize/hot_reload.spl") ?? ""
val engine_source = rt_file_read_text("src/compiler/40.mono/monomorphize/engine.spl") ?? ""
val integration_source = rt_file_read_text("src/compiler/40.mono/monomorphize_integration.spl") ?? ""

expect(cache_source.contains("use std.sdn.")).to_equal(false)
expect(hot_reload_source.contains("use std.sdn.")).to_equal(false)
expect(engine_source.contains("use hir_types.*")).to_equal(false)
expect(engine_source.contains("use hir_definitions.*")).to_equal(false)
expect(cache_source).to_contain("use std.common.sdn.parser (parse)")
expect(engine_source).to_contain("use compiler.hir.hir_types.*")
expect(integration_source).to_contain("val mod_keys = modules.keys()")
expect(integration_source.contains("for (k, v) in modules")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering monomorphization native-build regression.
- monomorphization native-build regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `6576b9f0068c2af75e7a3b68d05ec460a80853062af10306065436a235ab44bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6576b9f0068c2af75e7a3b68d05ec460a80853062af10306065436a235ab44bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6576b9f0068c2af75e7a3b68d05ec460a80853062af10306065436a235ab44bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl
mirror: doc/06_spec/01_unit/compiler/mono/monomorphization_native_build_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mono/monomorphization_native_build_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mono/monomorphization_native_build_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans block and field expressions without rt_enum_discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps direct mono compiles off root std.sdn and relative HIR imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
