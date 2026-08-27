# Static Component Table Generator (WP-14s)

> Generating a static table from a component catalog produces entries whose fold/no-fold verdicts match resolve_component exactly: placement=static folds, placement=auto folds only on a verified digest match, presence=off components are absent, and the generated module source bakes in ONLY the folded-static rows while dynamic ids stay external. A resolve failure (missing digest on placement=auto) aborts generation fail-closed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Component Table Generator (WP-14s)

Generating a static table from a component catalog produces entries whose fold/no-fold verdicts match resolve_component exactly: placement=static folds, placement=auto folds only on a verified digest match, presence=off components are absent, and the generated module source bakes in ONLY the folded-static rows while dynamic ids stay external. A resolve failure (missing digest on placement=auto) aborts generation fail-closed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Plan | doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B) |
| Source | `test/01_unit/lib/structural/static_component_table_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Generating a static table from a component catalog produces entries whose
fold/no-fold verdicts match resolve_component exactly: placement=static
folds, placement=auto folds only on a verified digest match, presence=off
components are absent, and the generated module source bakes in ONLY the
folded-static rows while dynamic ids stay external. A resolve failure
(missing digest on placement=auto) aborts generation fail-closed.

## Examples

A four-component catalog with one static, one auto+matching-digest, one
dynamic, one off yields folded={static, auto-matched}, dynamic={dynamic},
absent={off}, and a generated module whose entries() contain exactly the
two folded rows.

**Plan:** doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B)

## Scenarios

### static component table generation

#### classifies every component exactly as resolve_component does

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies every component exactly as resolve_component does
   - Expected: v equals `ok:folded=compiler.core,optimizer.basic:dynamic=loader.zstd:absent=aspect.log... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies every component exactly as resolve_component does")
val v = static_component_table_verdict(catalog_source(), digests_matching())
expect(v).to_equal("ok:folded=compiler.core,optimizer.basic:dynamic=loader.zstd:absent=aspect.log_debug")
```

</details>

#### bakes only folded-static rows into the generated module entries

- bakes only folded-static rows into the generated module entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bakes only folded-static rows into the generated module entries")
val src = static_component_table_module_source(catalog_source(), digests_matching())
expect(src.contains("rows.push(\"compiler.core|1|static|startup|presence=on,placement=static,activation=startup\")")).to_be(true)
expect(src.contains("rows.push(\"optimizer.basic|2|static|command|presence=auto,placement=auto,activation=command\")")).to_be(true)
expect(src.contains("rows.push(\"loader.zstd")).to_be(false)
expect(src.contains("aspect.log_debug")).to_be(false)
```

</details>

#### keeps dynamic components external in the generated module

- keeps dynamic components external in the generated module


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps dynamic components external in the generated module")
val src = static_component_table_module_source(catalog_source(), digests_matching())
expect(src.contains("ids.push(\"loader.zstd\")")).to_be(true)
expect(src.contains("ids.push(\"compiler.core\")")).to_be(false)
```

</details>

#### fails closed when a placement=auto component has no digest

- fails closed when a placement=auto component has no digest
   - Expected: v equals `err:resolve_failed:optimizer.basic:err:missing_impl_digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a placement=auto component has no digest")
var no_auto_digest: [text] = []
no_auto_digest.push("compiler.core|hc|hc")
val v = static_component_table_verdict(catalog_source(), no_auto_digest)
expect(v).to_equal("err:resolve_failed:optimizer.basic:err:missing_impl_digest")
```

</details>

#### fails closed on a malformed catalog

- fails closed on a malformed catalog


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a malformed catalog")
val v = static_component_table_verdict("component:\n  bogus: 1\n", digests_matching())
expect(v.starts_with("err:parse:")).to_be(true)
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


## Related Documentation

- **Plan:** `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b0cd77c351c8517e43fa3416040170bfbe6464382a3906ee5a98c4189a4db92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b0cd77c351c8517e43fa3416040170bfbe6464382a3906ee5a98c4189a4db92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b0cd77c351c8517e43fa3416040170bfbe6464382a3906ee5a98c4189a4db92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/structural/static_component_table_gen_spec.spl
mirror: doc/06_spec/01_unit/lib/structural/static_component_table_gen_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/structural/static_component_table_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/structural/static_component_table_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/structural/static_component_table_gen_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies every component exactly as resolve_component does' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/static_component_table_gen_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bakes only folded-static rows into the generated module entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/static_component_table_gen_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps dynamic components external in the generated module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
