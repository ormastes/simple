# tooling_facade_spec

> Purpose and audience: facade smoke verification for the nogc_async_mut src tooling

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tooling_facade_spec

Purpose and audience: facade smoke verification for the nogc_async_mut src tooling

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/tooling/tooling_facade_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: facade smoke verification for the nogc_async_mut src tooling
modules. Scope: regex utilities and easy-fix records reachable through the
facade re-exports. Audience: stdlib tooling maintainers.

research: doc/01_research/lib/collections_impl/collections.md ; plan: doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16_tldr.md ; architecture: doc/04_architecture/lib/runtime_family_stdlib_surface.md ; design: doc/05_design/lib/stdlib/aop_support_matrix.md

## Scenarios

### nogc_async_mut src tooling facade

#### re-exports regex utilities

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Regex utilities (expected show, folded, detail, or skip)


- Exercise the facade re-exports for this scenario
   - Text capture: after_step
   - Evidence: text output verified by 7 expected checks
   - Expected: regex_is_match(r"\d+", "build 42 passed") is true
   - Expected: m.text equals `128`
   - Expected: m.start equals `4`
   - Expected: regex_replace_all(r"\d+", "p50=12 p95=48", "N") equals `pN=N pN=N`
   - Expected: regex_split(r",\s*", "alpha, beta,gamma")[1] equals `beta`
   - Expected: is_valid_email("dev@example.com") is true
   - Expected: extract_numbers("x=7 y=11")[1] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-TOOLING-FACADE
step("Exercise the facade re-exports for this scenario")
expect(regex_is_match(r"\d+", "build 42 passed")).to_equal(true)
val found = regex_find(r"\d+", "run 128 ms")
match found:
    Some(m):
        expect(m.text).to_equal("128")
        expect(m.start).to_equal(4)  # oracle: 4 = index of "128" within "run 128 ms"
    nil:
        fail("regex_find did not return a match for digits")
expect(regex_replace_all(r"\d+", "p50=12 p95=48", "N")).to_equal("pN=N pN=N")
expect(regex_split(r",\s*", "alpha, beta,gamma")[1]).to_equal("beta")
expect(is_valid_email("dev@example.com")).to_equal(true)
expect(extract_numbers("x=7 y=11")[1]).to_equal("11")
```

</details>

#### re-exports easy-fix records

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Easy-fix records (expected show, folded, detail, or skip)


- Exercise the facade re-exports for this scenario
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: fix.is_safe() is true
   - Expected: fix.replacements.len() as i64 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-TOOLING-FACADE
step("Exercise the facade re-exports for this scenario")
val fix = EasyFix.create("demo.fix", "demo", FixConfidence.Safe)
fix.add_replacement(Replacement.create("file.spl", 1, 2, 1, 2, "x"))
expect(fix.is_safe()).to_equal(true)
expect(fix.replacements.len() as i64).to_equal(1)  # oracle: 1 = the single replacement record added above
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-LIB-TOOLING-FACADE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ee1aa3432b2be7c150e3dc914095f0115e84316ae8778a36ecc15512cde6922`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ee1aa3432b2be7c150e3dc914095f0115e84316ae8778a36ecc15512cde6922`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ee1aa3432b2be7c150e3dc914095f0115e84316ae8778a36ecc15512cde6922`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/lib/nogc_async_mut/src/tooling/tooling_facade_spec.spl
mirror: src/tooling/tooling_facade_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
src/tooling/tooling_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
src/tooling/tooling_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
