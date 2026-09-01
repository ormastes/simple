# Unit Return Bare Return Contract Specification

> Tests covering unit-returning functions accept a bare return.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Return Bare Return Contract Specification

## Scenarios

### unit-returning functions accept a bare return

#### a bare return in a `-> unit` fn is not a contract violation (repro)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a bare return in a `-> unit` fn is not a contract violation (repro)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bare return in a `-> unit` fn is not a contract violation (repro)")
# Exactly the shape of parser_validate_unit_suffix: guard clauses that
# bail out early with a bare `return`, then fall off the end.
fn validate_suffix(name: text) -> unit:
    if name == "":
        return
    if name == "i64":
        return
    ()
validate_suffix("")
validate_suffix("i64")
validate_suffix("meters")
assert_true(true)
```

</details>

#### a bare return in a `-> void` fn is not a contract violation (generalization)

- a bare return in a `-> void` fn is not a contract violation (generalization)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bare return in a `-> void` fn is not a contract violation (generalization)")
fn early_void(flag: bool) -> void:
    if flag:
        return
    ()
early_void(true)
early_void(false)
assert_true(true)
```

</details>

#### a bare return in a `-> ()` fn stays accepted (regression fence)

- a bare return in a `-> ()` fn stays accepted (regression fence)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bare return in a `-> ()` fn stays accepted (regression fence)")
# The one spelling that always worked; it must keep working.
fn early_paren(flag: bool) -> ():
    if flag:
        return
    ()
early_paren(true)
early_paren(false)
assert_true(true)
```

</details>

#### a `-> unit` fn with no return statement at all still works

- a `-> unit` fn with no return statement at all still works


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a `-> unit` fn with no return statement at all still works")
fn no_return(x: i64) -> unit:
    val _ = x + 1
    ()
no_return(3)
assert_true(true)
```

</details>

#### the non-optional contract still fires for a real non-unit return type

- the non-optional contract still fires for a real non-unit return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the non-optional contract still fires for a real non-unit return type")
# The fix must not disarm the contract: `unit`/`void` are void
# spellings, not a blanket exemption for every declared return type.
val src = "fn f() -> i64:\n    return nil\n\nfn main() -> i64:\n    f()\n"
val path = "/tmp/unit_return_contract_negative.spl"
val _ = file_write(path, src)
var bin = env_get("SIMPLE_BIN") ?? ""
if bin.len() == 0:
    bin = "bin/simple"
val (stdout, stderr, _code) = process_run("/bin/sh", ["-c", bin + " run " + path + " 2>&1"])
expect(stdout + stderr).to_contain("non-optional return contract")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/unit_return_bare_return_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering unit-returning functions accept a bare return.
- unit-returning functions accept a bare return

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `76d79ce6b600cb6ebd5a686c01a11520f0cefd8c24be1b5b56234f4d1a90439e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76d79ce6b600cb6ebd5a686c01a11520f0cefd8c24be1b5b56234f4d1a90439e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76d79ce6b600cb6ebd5a686c01a11520f0cefd8c24be1b5b56234f4d1a90439e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/unit_return_bare_return_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/unit_return_bare_return_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/unit_return_bare_return_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/unit_return_bare_return_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/unit_return_bare_return_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a bare return in a `-> unit` fn is not a contract violation (repro)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/unit_return_bare_return_contract_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a bare return in a `-> void` fn is not a contract violation (generalization)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/unit_return_bare_return_contract_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a bare return in a `-> ()` fn stays accepted (regression fence)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
