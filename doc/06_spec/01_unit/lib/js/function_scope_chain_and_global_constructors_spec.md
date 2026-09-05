# Function Scope Chain And Global Constructors Specification

> Tests covering JS engine function scope chain and global constructors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Function Scope Chain And Global Constructors Specification

## Scenarios

### JS engine function scope chain and global constructors

<details>
<summary>Advanced: runs a for loop declared inside a function body</summary>

#### runs a for loop declared inside a function body

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs a for loop declared inside a function body
   - Expected: top equals `3.0`
   - Expected: infn equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs a for loop declared inside a function body")
val rt = js_runtime_with_default_logger("scope-spec")
val top = eval_num(rt, "var s=0; for (var i=0;i<3;i=i+1){ s=s+i; } s")
expect(top).to_equal(3.0)
val infn = eval_num(rt, "function h(){ var s=0; for (var i=0;i<3;i=i+1){ s=s+i; } return s; } h()")
expect(infn).to_equal(3.0)
```

</details>


</details>

<details>
<summary>Advanced: resolves outer function locals from nested loop envs (getElementById shim shape)</summary>

#### resolves outer function locals from nested loop envs (getElementById shim shape)

- resolves outer function locals from nested loop envs (getElementById shim shape)
   - Expected: found equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves outer function locals from nested loop envs (getElementById shim shape)")
val rt = js_runtime_with_default_logger("scope-spec2")
val found = eval_num(rt,
    "var q={}; q.f=function(id){ var all=[1,2,3]; " +
    "for (var i=0;i<all.length;i=i+1){ if(all[i]===id){return i;} } " +
    "return -1; }; q.f(2)")
expect(found).to_equal(1.0)
```

</details>


</details>

#### provides global String/Number/Boolean conversion functions

- provides global String/Number/Boolean conversion functions
   - Expected: eval_text(rt, "String(5)") equals `5`
   - Expected: eval_num(rt, "Number('4')+1") equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("provides global String/Number/Boolean conversion functions")
val rt = js_runtime_with_default_logger("ctor-spec")
expect(eval_text(rt, "String(5)")).to_equal("5")
expect(eval_num(rt, "Number('4')+1")).to_equal(5.0)
val b = rt.eval("Boolean('x')")
match b:
    Ok(v):
        match v:
            JsValue.Boolean(flag): expect(flag).to_equal(true)
            _: fail("Boolean('x') did not return a boolean")
    Err(e): fail("Boolean('x') errored: {e.message}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS engine function scope chain and global constructors.
- JS engine function scope chain and global constructors

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89a8f6bf27619f4a129696d4fa821522ec2a1a3e976c0c493afb837452b7f88a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89a8f6bf27619f4a129696d4fa821522ec2a1a3e976c0c493afb837452b7f88a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89a8f6bf27619f4a129696d4fa821522ec2a1a3e976c0c493afb837452b7f88a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl
mirror: doc/06_spec/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs a for loop declared inside a function body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves outer function locals from nested loop envs (getElementById shim shape)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides global String/Number/Boolean conversion functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
