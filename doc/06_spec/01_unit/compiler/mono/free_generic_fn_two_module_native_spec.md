# Free Generic Fn Two Module Native Specification

> Tests covering free generic fn called from another module at two types, hir_visitor walker shape: fn-reference + unannotated constructor let.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Free Generic Fn Two Module Native Specification

## Scenarios

### free generic fn called from another module at two types

#### lowers both modules with no Phase A generic-fn fatal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers both modules with no Phase A generic-fn fatal
   - Expected: generic_fatals equals `0`
   - Expected: low.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers both modules with no Phase A generic-fn fatal")
val low = lower_pair()
var generic_fatals = 0
for m in low.errors:
    if m.contains("generic functions are not supported"):
        generic_fatals = generic_fatals + 1
expect(generic_fatals).to_equal(0)
expect(low.errors.len()).to_equal(0)
```

</details>

#### specializes pick_second at i64 and Acc, plus same$i64, with no unresolved call site

- specializes pick_second at i64 and Acc, plus same$i64, with no unresolved call site
   - Expected: diags.len() equals `0`
   - Expected: stats.generic_functions_found equals `2`
   - Expected: stats.call_sites_found equals `4`
   - Expected: stats.specializations_created equals `3`
   - Expected: stats.unresolved_generic_calls equals `0`
   - Expected: lib_fns contains `pick_second$i64`
   - Expected: lib_fns contains `pick_second$Acc`
   - Expected: lib_fns contains `same$i64`
   - Expected: lib_fns does not contain `pick_second`
   - Expected: lib_fns does not contain `same`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("specializes pick_second at i64 and Acc, plus same$i64, with no unresolved call site")
val low = lower_pair()
val (mono, stats, diags) = run_monomorphization_with_diagnostics(low.modules)
expect(diags.len()).to_equal(0)
expect(stats.generic_functions_found).to_equal(2)
expect(stats.call_sites_found).to_equal(4)
expect(stats.specializations_created).to_equal(3)
expect(stats.unresolved_generic_calls).to_equal(0)
val lib_fns = function_names(mono["lib"])
expect(lib_fns.contains("pick_second$i64")).to_equal(true)
expect(lib_fns.contains("pick_second$Acc")).to_equal(true)
expect(lib_fns.contains("same$i64")).to_equal(true)
# consumed templates are dropped
expect(lib_fns.contains("pick_second")).to_equal(false)
expect(lib_fns.contains("same")).to_equal(false)
```

</details>

#### repoints main's call sites at the mangled names MIR resolves by

- repoints main's call sites at the mangled names MIR resolves by
   - Expected: i64_hits equals `1`
   - Expected: acc_hits equals `1`
   - Expected: same_hits equals `1`
   - Expected: template_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("repoints main's call sites at the mangled names MIR resolves by")
# This harness lowers without the driver's entry-closure import
# qualification, so the callee display name is bare `pick_second`;
# under the driver it is `lib.pick_second` and the rewrite keeps that
# qualifier (mono_requalify). Assert on the function-name suffix.
val low = lower_pair()
val (mono, _stats, _diags) = run_monomorphization_with_diagnostics(low.modules)
val callees = callee_names_in_main(mono["main"])
var i64_hits = 0
var acc_hits = 0
var same_hits = 0
var template_hits = 0
for c in callees:
    val ct: text = c
    if ct.ends_with("pick_second$i64"):
        i64_hits = i64_hits + 1
    if ct.ends_with("pick_second$Acc"):
        acc_hits = acc_hits + 1
    if ct.ends_with("same$i64"):
        same_hits = same_hits + 1
    if ct.ends_with("pick_second") or ct.ends_with("same"):
        template_hits = template_hits + 1
expect(i64_hits).to_equal(1)
expect(acc_hits).to_equal(1)
expect(same_hits).to_equal(1)
expect(template_hits).to_equal(0)
```

</details>

### hir_visitor walker shape: fn-reference + unannotated constructor let

#### infers C = Scan from the let and the function reference, 1 specialization

- infers C = Scan from the let and the function reference, 1 specialization
   - Expected: low.errors.len() equals `0`
   - Expected: diags.len() equals `0`
   - Expected: stats.call_sites_found equals `1`
   - Expected: stats.specializations_created equals `1`
   - Expected: stats.unresolved_generic_calls equals `0`
   - Expected: fns contains `walk_node$Scan`
   - Expected: fns does not contain `walk_node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("infers C = Scan from the let and the function reference, 1 specialization")
val low = lower_two("walk_lib", WALK_LIB_SRC, "walk_main", WALK_MAIN_SRC)
expect(low.errors.len()).to_equal(0)
val (mono, stats, diags) = run_monomorphization_with_diagnostics(low.modules)
expect(diags.len()).to_equal(0)
expect(stats.call_sites_found).to_equal(1)
expect(stats.specializations_created).to_equal(1)
expect(stats.unresolved_generic_calls).to_equal(0)
val fns = function_names(mono["walk_lib"])
expect(fns.contains("walk_node$Scan")).to_equal(true)
expect(fns.contains("walk_node")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering free generic fn called from another module at two types, hir_visitor walker shape: fn-reference + unannotated constructor let.
- free generic fn called from another module at two types
- hir_visitor walker shape: fn-reference + unannotated constructor let

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `1e1d9c47fcccef72508a6a586ab4ec446fec9276423f8ac76c83f1d25a94a162`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e1d9c47fcccef72508a6a586ab4ec446fec9276423f8ac76c83f1d25a94a162`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e1d9c47fcccef72508a6a586ab4ec446fec9276423f8ac76c83f1d25a94a162`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl
mirror: doc/06_spec/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers both modules with no Phase A generic-fn fatal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'specializes pick_second at i64 and Acc, plus same$i64, with no unresolved call site' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repoints main's call sites at the mangled names MIR resolves by' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
