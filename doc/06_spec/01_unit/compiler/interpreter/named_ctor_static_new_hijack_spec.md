# Named Ctor Static New Hijack Specification

> Tests covering named-argument class construction versus static fn new.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Named Ctor Static New Hijack Specification

## Scenarios

### named-argument class construction versus static fn new

#### binds field-named arguments to fields, in either order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds field-named arguments to fields, in either order
- Controls — these already pass, and prove the named binder runs at all
- Reversed argument order discriminates a name-honouring binder from a positional one


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds field-named arguments to fields, in either order")
step("Controls — these already pass, and prove the named binder runs at all")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PASS field_names_build_struct_id")
expect(interp).to_contain("PASS field_names_build_struct_size")

step("Reversed argument order discriminates a name-honouring binder from a positional one")
expect(interp).to_contain("PASS reversed_order_id")
expect(interp).to_contain("PASS reversed_order_size")
```

</details>

#### still reaches the static constructor through an explicit .new call

- still reaches the static constructor through an explicit .new call
- The fix must not break the legitimate route to `static fn new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still reaches the static constructor through an explicit .new call")
step("The fix must not break the legitimate route to `static fn new`")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PASS explicit_new_still_reaches_static")
```

</details>

#### does not dispatch a named literal to static fn new on the parameter names

- does not dispatch a named literal to static fn new on the parameter names
- `path` is a parameter of `new` and NOT a field of Font; the sentinel id=77 is reachable only from inside `new`'s body


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not dispatch a named literal to static fn new on the parameter names")
step("`path` is a parameter of `new` and NOT a field of Font; the sentinel id=77 is reachable only from inside `new`'s body")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PASS param_names_do_not_hijack")
```

</details>

#### does not dispatch on the run path either

- does not dispatch on the run path either
- The same hijack reproduces under `bin/simple run`, so the fix must cover both engines
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not dispatch on the run path either")
step("The same hijack reproduces under `bin/simple run`, so the fix must cover both engines")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS param_names_do_not_hijack")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("NAMED_CTOR_HIJACK PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering named-argument class construction versus static fn new.
- named-argument class construction versus static fn new

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

- Canonical SPipe generation for source `a0a2de53dc3e99d9e07173924a6ac667265289ac272505df8ffc38c7a37fae8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0a2de53dc3e99d9e07173924a6ac667265289ac272505df8ffc38c7a37fae8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0a2de53dc3e99d9e07173924a6ac667265289ac272505df8ffc38c7a37fae8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds field-named arguments to fields, in either order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still reaches the static constructor through an explicit .new call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/named_ctor_static_new_hijack_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not dispatch a named literal to static fn new on the parameter names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
