# Critical-profile `Any` escape analysis

> `AnyEscapeChecker` enforces plan §8.1: in the `critical` profile the erased top

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Critical-profile `Any` escape analysis

`AnyEscapeChecker` enforces plan §8.1: in the `critical` profile the erased top

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | In Progress |
| Research | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md |
| Source | `test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`AnyEscapeChecker` enforces plan §8.1: in the `critical` profile the erased top
type `Any` is legal only inside an `unsafe` region carrying the `type_erasure`
capability, and an erased value may not leave that region except as the result
of a checked conversion. This spec pins both diagnostics against real typed HIR.

## Scope and Preconditions

Each scenario parses a fixture under `test/fixtures/any_escape/`, lowers it to
HIR, and runs `any_escape_check`. Nothing is decided from source text: the
checker reads `HirTypeKind.Any` off resolved `HirType` values.

## Primary Workflow

`E-MC-ANY-001` fires where an `Any` originates outside a granted region.
`E-MC-ANY-002` fires where an erased value escapes one. Neither fires on code
that has no `Any`, nor on the sanctioned §8.6 checked-conversion boundary.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `type_erasure` | The unsafe capability that licenses `Any` (§8.1) |
| origin | A site where an `Any` value comes into existence |
| escape | An erased value leaving its region: store, return, capture, await, call, operator |

## Related Specifications

- doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md §8.5, §17.1, §17.2

## Evidence and Provenance

Fixtures are executable inputs, not prose. The negative cases (`clean`,
`checked_downcast_ok`) are load-bearing: without them a checker that flagged
everything would pass the positive cases.

## Recovery and Troubleshooting

A finding names the function and the diagnostic class. Replace the `Any` with a
monomorphized generic, a closed sum type, a typed interface, or move it inside
an `unsafe` region annotated `@unsafe(capabilities: [type_erasure])`.

## Compatibility and Limitations

The `type_erasure` GRANT is supplied through `AnyEscapeProfile` because HIR does
not yet carry unsafe capabilities — see
doc/08_tracking/bug/unsafe_capabilities_not_carried_into_hir_2026-08-21.md.

## Scenarios

### Critical Any escape analysis

#### reports E-MC-ANY-001 for an Any bound in a safe function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports E-MC-ANY-001 for an Any bound in a safe function
- lower a fixture whose safe function declares `val raw: Any`
- the origin is reported as E-MC-ANY-001 / outside_unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports E-MC-ANY-001 for an Any bound in a safe function")
step("lower a fixture whose safe function declares `val raw: Any`")
val found = check_fixture("any_in_safe_fn", [])
step("the origin is reported as E-MC-ANY-001 / outside_unsafe")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_be_greater_than(0)
```

</details>

#### reports E-MC-ANY-002 when an erased value is returned from a granted region

- reports E-MC-ANY-002 when an erased value is returned from a granted region
- lower a fixture whose type_erasure region returns its raw Any
- the escape is reported as E-MC-ANY-002 / escape_return
- and it is an escape, not an origin: the region grants type_erasure
   - Expected: count_of(found, "E-MC-ANY-001/outside_unsafe") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports E-MC-ANY-002 when an erased value is returned from a granted region")
step("lower a fixture whose type_erasure region returns its raw Any")
val found = check_fixture("any_returned_from_boundary", ["leak_raw"])
step("the escape is reported as E-MC-ANY-002 / escape_return")
expect(count_of(found, "E-MC-ANY-002/escape_return")).to_be_greater_than(0)
step("and it is an escape, not an origin: the region grants type_erasure")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_equal(0)
```

</details>

#### is silent on code that contains no Any at all

- is silent on code that contains no Any at all
- lower a fixture with only concrete types
- nothing is reported
   - Expected: found.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is silent on code that contains no Any at all")
step("lower a fixture with only concrete types")
val found = check_fixture("clean", [])
step("nothing is reported")
expect(found.len()).to_equal(0)
```

</details>

#### is silent when a checked conversion's concrete result leaves the region

- is silent when a checked conversion's concrete result leaves the region
- lower a fixture whose region converts before the value leaves
- neither the origin nor the call is reported
   - Expected: found.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is silent when a checked conversion's concrete result leaves the region")
step("lower a fixture whose region converts before the value leaves")
val found = check_fixture("checked_downcast_ok", ["checked_downcast", "decode"])
step("neither the origin nor the call is reported")
expect(found.len()).to_equal(0)
```

</details>

#### reports the origin again when the region is not granted type_erasure

- reports the origin again when the region is not granted type_erasure
- lower the boundary fixture with an EMPTY grant list
- the Any inside the ungranted unsafe block is an E-MC-ANY-001 origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the origin again when the region is not granted type_erasure")
step("lower the boundary fixture with an EMPTY grant list")
val found = check_fixture("checked_downcast_ok", [])
step("the Any inside the ungranted unsafe block is an E-MC-ANY-001 origin")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_be_greater_than(0)
```

</details>

#### is silent on an imported `T?` parameter and the values extracted from it

- is silent on an imported `T?` parameter and the values extracted from it
- lower a fixture whose parameter is `ImportedType?`, compared with nil and match-extracted
- no origin and no operator escape is reported
   - Expected: count_of(found, "E-MC-ANY-001/outside_unsafe") equals `0`
   - Expected: count_of(found, "E-MC-ANY-002/escape_operator") equals `0`
   - Expected: found.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is silent on an imported `T?` parameter and the values extracted from it")
step("lower a fixture whose parameter is `ImportedType?`, compared with nil and match-extracted")
val found = check_fixture("imported_optional_param", [])
step("no origin and no operator escape is reported")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_equal(0)
expect(count_of(found, "E-MC-ANY-002/escape_operator")).to_equal(0)
expect(found.len()).to_equal(0)
```

</details>

#### reports a written `Any?` parameter as an erased value

- reports a written `Any?` parameter as an erased value
- lower a fixture whose safe function takes `raw: Any?` and evaluates `raw != nil`
- the optional-wrapped erased parameter is an E-MC-ANY-001 origin
- and the operator on it is an E-MC-ANY-002 escape


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a written `Any?` parameter as an erased value")
step("lower a fixture whose safe function takes `raw: Any?` and evaluates `raw != nil`")
val found = check_fixture("written_any_optional", [])
step("the optional-wrapped erased parameter is an E-MC-ANY-001 origin")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_be_greater_than(0)
step("and the operator on it is an E-MC-ANY-002 escape")
expect(count_of(found, "E-MC-ANY-002/escape_operator")).to_be_greater_than(0)
```

</details>

#### still reports a real bare `Any` parameter applied to an operator

- still reports a real bare `Any` parameter applied to an operator
- lower a fixture whose safe function takes `raw: Any` and evaluates `raw != nil`
- the parameter is an E-MC-ANY-001 origin
- and the operator on it is an E-MC-ANY-002 escape


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still reports a real bare `Any` parameter applied to an operator")
step("lower a fixture whose safe function takes `raw: Any` and evaluates `raw != nil`")
val found = check_fixture("any_param_operator", [])
step("the parameter is an E-MC-ANY-001 origin")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_be_greater_than(0)
step("and the operator on it is an E-MC-ANY-002 escape")
expect(count_of(found, "E-MC-ANY-002/escape_operator")).to_be_greater_than(0)
```

</details>

#### survives a desugared binding that carries no declared type

- survives a desugared binding that carries no declared type
- lower a fixture whose tuple destructure yields `Let(sym, nil, init)`
- the pass completes and reports nothing -- no `Any` is present
   - Expected: found.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("survives a desugared binding that carries no declared type")
step("lower a fixture whose tuple destructure yields `Let(sym, nil, init)`")
val found = check_fixture("tuple_destructure_binding", [])
step("the pass completes and reports nothing -- no `Any` is present")
expect(found.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MC-ANY-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eefcd2acccc24a17073c79a726bf03370ecc24c568d6a1af18eb33781e62855d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eefcd2acccc24a17073c79a726bf03370ecc24c568d6a1af18eb33781e62855d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eefcd2acccc24a17073c79a726bf03370ecc24c568d6a1af18eb33781e62855d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/any_escape/any_escape_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/semantics/any_escape/any_escape_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports E-MC-ANY-001 for an Any bound in a safe function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports E-MC-ANY-002 when an erased value is returned from a granted region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is silent on code that contains no Any at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
