# Mono pass consumes SOURCE-lowered generic templates (inferred type args, fixed point)

> Purpose: Prove that mono pass on source-lowered generics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mono pass consumes SOURCE-lowered generic templates (inferred type args, fixed point)

Purpose: Prove that mono pass on source-lowered generics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that mono pass on source-lowered generics.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### mono pass on source-lowered generics

#### specializes a free fn whose single type argument is INFERRED from an i64 literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- specializes a free fn whose single type argument is INFERRED from an i64 literal
- Verify: specializes a free fn whose single type argument is INFERRED from an i64 literal
   - Expected: stats.specializations_created equals `1`
   - Expected: stats.unresolved_generic_calls equals `0`
   - Expected: count_named(om, "ident$i64") equals `1`
   - Expected: count_named(om, "ident") equals `0`
   - Expected: post_mono_report_total(r) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("specializes a free fn whose single type argument is INFERRED from an i64 literal")
step("Verify: specializes a free fn whose single type argument is INFERRED from an i64 literal")
# @req: REQ-COMPILER-MONO-001
val src = "fn ident<T>(v: T) -> T:\n    v\n\nfn main() -> i64:\n    val x: i64 = ident(7)\n    x\n"
val parsed = parse_full_frontend(src, "testdata/mono_infer_ident.spl", "mono_infer_ident", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/mono_infer_ident.spl")
val hir = hl.lower_module(parsed)
var mods: Dict<text, HirModule> = {}
mods["m"] = hir
val (out, stats) = run_monomorphization(mods)
expect(stats.specializations_created).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(stats.unresolved_generic_calls).to_equal(0)  # oracle: 0 — named expected value from the requirement
val om: HirModule = out["m"]
expect(count_named(om, "ident$i64")).to_equal(1)
expect(count_named(om, "ident")).to_equal(0)
val r = post_mono_verify_modules(out)
expect(post_mono_report_total(r)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### rewrites a generic call nested inside an if arm

- rewrites a generic call nested inside an if arm
- Verify: rewrites a generic call nested inside an if arm
   - Expected: stats.specializations_created equals `1`
   - Expected: r.generic_call equals `0`
   - Expected: r.generic_emitted_definition equals `0`
   - Expected: post_mono_report_total(r) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rewrites a generic call nested inside an if arm")
step("Verify: rewrites a generic call nested inside an if arm")
val src = "fn ident<T>(v: T) -> T:\n    v\n\nfn pick(b: bool) -> i64:\n    if b:\n        ident(1)\n    else:\n        2\n"
val parsed = parse_full_frontend(src, "testdata/mono_infer_if.spl", "mono_infer_if", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/mono_infer_if.spl")
val hir = hl.lower_module(parsed)
var mods: Dict<text, HirModule> = {}
mods["m"] = hir
val (out, stats) = run_monomorphization(mods)
expect(stats.specializations_created).to_equal(1)  # oracle: 1 — named expected value from the requirement
val r = post_mono_verify_modules(out)
expect(r.generic_call).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(r.generic_emitted_definition).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(post_mono_report_total(r)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reaches a fixed point: a specialization's body requests a deeper instantiation

- reaches a fixed point: a specialization's body requests a deeper instantiation
- Verify: reaches a fixed point: a specialization's body requests a deeper instantiation
   - Expected: stats.specializations_created equals `2`
   - Expected: stats.unresolved_generic_calls equals `0`
   - Expected: count_named(om, "wrap$i64") equals `1`
   - Expected: count_named(om, "wrap$arr_i64") equals `1`
   - Expected: count_named(om, "wrap") equals `0`
   - Expected: post_mono_report_total(r) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reaches a fixed point: a specialization's body requests a deeper instantiation")
step("Verify: reaches a fixed point: a specialization's body requests a deeper instantiation")
val src = "fn wrap<T>(v: T) -> [T]:\n    [v]\n\nfn root() -> [[i64]]:\n    wrap(wrap(1))\n"
val parsed = parse_full_frontend(src, "testdata/mono_fixed_point.spl", "mono_fixed_point", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/mono_fixed_point.spl")
val hir = hl.lower_module(parsed)
var mods: Dict<text, HirModule> = {}
mods["m"] = hir
val (out, stats) = run_monomorphization(mods)
expect(stats.specializations_created).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(stats.unresolved_generic_calls).to_equal(0)  # oracle: 0 — named expected value from the requirement
val om: HirModule = out["m"]
expect(count_named(om, "wrap$i64")).to_equal(1)
expect(count_named(om, "wrap$arr_i64")).to_equal(1)
expect(count_named(om, "wrap")).to_equal(0)
val r = post_mono_verify_modules(out)
expect(post_mono_report_total(r)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### deduplicates: two call sites at the same type share one specialization

- deduplicates: two call sites at the same type share one specialization
- Verify: deduplicates: two call sites at the same type share one specialization
   - Expected: stats.call_sites_found equals `2`
   - Expected: stats.specializations_created equals `1`
   - Expected: post_mono_report_total(r) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("deduplicates: two call sites at the same type share one specialization")
step("Verify: deduplicates: two call sites at the same type share one specialization")
val src = "fn ident<T>(v: T) -> T:\n    v\n\nfn a() -> i64:\n    ident(1)\n\nfn b() -> i64:\n    ident(2)\n"
val parsed = parse_full_frontend(src, "testdata/mono_dedup.spl", "mono_dedup", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/mono_dedup.spl")
val hir = hl.lower_module(parsed)
var mods: Dict<text, HirModule> = {}
mods["m"] = hir
val (out, stats) = run_monomorphization(mods)
expect(stats.call_sites_found).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(stats.specializations_created).to_equal(1)  # oracle: 1 — named expected value from the requirement
val r = post_mono_verify_modules(out)
expect(post_mono_report_total(r)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### fails closed: an uninferable call keeps the template, is diagnosed, and the verifier counts it

- fails closed: an uninferable call keeps the template, is diagnosed, and the verifier counts it
- Verify: fails closed: an uninferable call keeps the template, is diagnosed, and the verifier counts it
   - Expected: stats.specializations_created equals `0`
   - Expected: stats.unresolved_generic_calls equals `1`
   - Expected: diags.len() equals `1`
   - Expected: count_named(om, "ident") equals `1`
   - Expected: r.generic_emitted_definition equals `1`
   - Expected: r.generic_call equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed: an uninferable call keeps the template, is diagnosed, and the verifier counts it")
step("Verify: fails closed: an uninferable call keeps the template, is diagnosed, and the verifier counts it")
# `y` has no annotation and its initializer is a method call whose
# result type this pass cannot know, so `T` stays unbound.
val src = "fn ident<T>(v: T) -> T:\n    v\n\nfn root(d: Dict<text, i64>) -> i64:\n    val y = d.get(\"k\")\n    ident(y)\n"
val parsed = parse_full_frontend(src, "testdata/mono_unresolved.spl", "mono_unresolved", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/mono_unresolved.spl")
val hir = hl.lower_module(parsed)
var mods: Dict<text, HirModule> = {}
mods["m"] = hir
val (out, stats, diags) = run_monomorphization_with_diagnostics(mods)
expect(stats.specializations_created).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(stats.unresolved_generic_calls).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(diags.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(diags[0]).to_contain("E-MONO-032")
val om: HirModule = out["m"]
expect(count_named(om, "ident")).to_equal(1)
val r = post_mono_verify_modules(out)
expect(r.generic_emitted_definition).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(r.generic_call).to_equal(1)  # oracle: 1 — named expected value from the requirement
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
- `REQ-COMPILER-MONO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a86abf31627c5a42c26c203a4d868d75ad8f90bca31a2ea6e24423f7e9c0d73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a86abf31627c5a42c26c203a4d868d75ad8f90bca31a2ea6e24423f7e9c0d73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a86abf31627c5a42c26c203a4d868d75ad8f90bca31a2ea6e24423f7e9c0d73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.spl
mirror: doc/06_spec/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'specializes a free fn whose single type argument is INFERRED from an i64 literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites a generic call nested inside an if arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/mono_source_inference_fixed_point_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches a fixed point: a specialization's body requests a deeper instantiation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
