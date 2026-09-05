# LLVM Aggregate Shared Binding Contract

> translate_call_indirect derives the indirect-call destination and return type

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Aggregate Shared Binding Contract

translate_call_indirect derives the indirect-call destination and return type

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

translate_call_indirect derives the indirect-call destination and return type
without reassignment (decay-safe `val` bindings). Behaviorally: a program
whose only foreign edge is an indirect call through a first-class function
value must compile cleanly, and an indirect call with an unresolved callee
must fail as a compile error rather than crashing the backend.

## Scenarios

### LLVM aggregate strict shared bindings

#### an indirect call through a function value compiles cleanly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compile a fixture whose call edge is an indirect call through a function value
   - Expected: result.is_ok() is true
   - Expected: pr.exit_code equals `0`
   - Expected: "${message}" equals `__unreachable__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile a fixture whose call edge is an indirect call through a function value")
# evidence(terminal_grid): compiler exit status asserted below is the complete typed oracle
val path = _write_fixture("indirect_ok.spl",
    "fn apply(f: fn(i64) -> i64, x: i64) -> i64:\n    return f(x)\nfn inc(v: i64) -> i64:\n    return v + 1\nfn main() -> i64:\n    return apply(inc, 41)\n")
val result = run_process("bin/simple", ["compile", path])
expect(result.is_ok()).to_equal(true)
match result:
    case Ok(pr):
        expect(pr.exit_code).to_equal(0)  # oracle: a well-formed indirect call must compile without crashing the backend
    case Err(message):
        expect("${message}").to_equal("__unreachable__")
```

</details>

#### an indirect call with an unresolved callee fails as a compile error

- compile a fixture that indirect-calls an unresolved import
   - Expected: result.is_ok() is true
   - Expected: pr.exit_code > 0 is true
   - Expected: "${message}" equals `__unreachable__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile a fixture that indirect-calls an unresolved import")
# evidence(terminal_grid): compiler exit status asserted below is the complete typed oracle
val path = _write_fixture("indirect_unresolved.spl",
    "extern fn missing_fn(x: i64) -> i64\nfn main() -> i64:\n    val f = missing_fn\n    return f(1)\n")
val result = run_process("bin/simple", ["compile", path])
expect(result.is_ok()).to_equal(true)
match result:
    case Ok(pr):
        expect(pr.exit_code > 0).to_equal(true)  # oracle: an unresolved callee is a compile error, never a silent success
    case Err(message):
        expect("${message}").to_equal("__unreachable__")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f9cc3df961d369a2d50733d713de62822820905a9da6c1c8f40d7ad2256e4c68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f9cc3df961d369a2d50733d713de62822820905a9da6c1c8f40d7ad2256e4c68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f9cc3df961d369a2d50733d713de62822820905a9da6c1c8f40d7ad2256e4c68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
