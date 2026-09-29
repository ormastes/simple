# Parse Collect All Errors Specification

> Tests covering parse reaches the end of all sources.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse Collect All Errors Specification

## Scenarios

### parse reaches the end of all sources

#### reports all three broken files in one run

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports all three broken files in one run
   - Expected: ok is false
   - Expected: ctx.poisoned_module_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports all three broken files in one run")
var driver = broken_tree_driver()
val (ctx, ok) = driver.parse_all_impl()
expect(ok).to_equal(false)
val blob = error_blob(ctx.errors)
print "[collect-all] errors:\n{blob}"
expect(blob).to_contain("build/collect/broken_one.spl")
expect(blob).to_contain("build/collect/broken_two.spl")
expect(blob).to_contain("build/collect/broken_three.spl")
expect(ctx.poisoned_module_count()).to_equal(3)
```

</details>

#### keeps parsing sources that follow a broken one

- keeps parsing sources that follow a broken one
   - Expected: ctx.modules.contains_key("fixture.clean_a") is true
   - Expected: ctx.modules.contains_key("fixture.clean_b") is true
   - Expected: ctx.modules.contains_key("fixture.broken_two") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps parsing sources that follow a broken one")
var driver = broken_tree_driver()
val (ctx, _) = driver.parse_all_impl()
expect(ctx.modules.contains_key("fixture.clean_a")).to_equal(true)
expect(ctx.modules.contains_key("fixture.clean_b")).to_equal(true)
expect(ctx.modules.contains_key("fixture.broken_two")).to_equal(false)
```

</details>

#### still succeeds on a clean tree

- still succeeds on a clean tree
   - Expected: ok is true
   - Expected: ctx.errors.len() equals `0`
   - Expected: ctx.poisoned_module_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still succeeds on a clean tree")
var driver = fixture_driver([
    fixture_source("build/collect/clean_a.spl",
        "fn clean_a() -> i64:\n    return 1\n", "fixture.clean_a"),
    fixture_source("build/collect/clean_b.spl",
        "fn clean_b() -> i64:\n    return 2\n", "fixture.clean_b")
])
val (ctx, ok) = driver.parse_all_impl()
expect(ok).to_equal(true)
expect(ctx.errors.len()).to_equal(0)
expect(ctx.poisoned_module_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/parse_collect_all_errors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parse reaches the end of all sources.
- parse reaches the end of all sources

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60bbd299c329dbaec9be547e089bb26f8175e2b0c69794d5e6631122b464c4a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60bbd299c329dbaec9be547e089bb26f8175e2b0c69794d5e6631122b464c4a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60bbd299c329dbaec9be547e089bb26f8175e2b0c69794d5e6631122b464c4a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/driver/parse_collect_all_errors_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/parse_collect_all_errors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/parse_collect_all_errors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/parse_collect_all_errors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/parse_collect_all_errors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/parse_collect_all_errors_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports all three broken files in one run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/parse_collect_all_errors_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps parsing sources that follow a broken one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/parse_collect_all_errors_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still succeeds on a clean tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
