# Copying a typed array between variables preserves its elements

> Anyone who writes `val b = a` where `a` is a `[u64]` or `[u8]` expects `b` to

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Copying a typed array between variables preserves its elements

Anyone who writes `val b = a` where `a` is a `[u64]` or `[u8]` expects `b` to

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | In Progress |
| Source | `test/unit/compiler/typed_array_variable_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Anyone who writes `val b = a` where `a` is a `[u64]` or `[u8]` expects `b` to
hold the same values. Today it does not: the copy keeps the correct length and
zeroes every element, with no error and no warning. This scenario exists so
that defect can never again be discovered by way of a wrong cryptographic
answer.

## Scope and Preconditions

Covers the value semantics of binding an existing typed-array variable to a new
name — `val`-to-`val`, `val`-to-`var`, `var`-to-`var`, and the array-literal
form. No host capability is required.

## Primary Workflow

A developer builds an array, binds it to another name, and reads an element
back. The element read must equal the element written, regardless of which
binding form carried it there.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Binding form | Whether the right-hand side is a call, a literal, or another variable |
| Length-preserving zeroing | The failure mode: `.length()` is right, every element is 0 |
| Swap idiom | `val t = a; a = b; b = t` — destructive while this defect is live |

## Evidence and Provenance

Measured 2026-08-17 on the deployed seed. Binding from a direct function call
returned 5 as written; every variable-to-variable binding returned 0 while
reporting length 2. Filed as
`doc/08_tracking/bug/typed_array_variable_binding_zeroes_elements_2026-08-17.md`.

## Recovery and Troubleshooting

While this is RED, do not treat a typed array as copyable by rebinding. Re-derive
the value through a function call at each use, and never rely on the three-step
swap idiom for arrays. A green run here means the workaround in
`src/lib/nogc_async_mut_noalloc/tls/x25519.spl` can be reverted to the direct
binding.

## Compatibility and Limitations

Asserts `[u64]`, the element type where the defect was measured. Other element
types are untested and may behave differently.

## Scenarios

### A typed array copied to a new name keeps its elements

#### carries values through a val-to-val binding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries values through a val-to-val binding
- Build a [u64] whose first element is 5
- Bind it to a second val and read element 0
   - Expected: _first_via_val_to_val() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries values through a val-to-val binding")
step("Build a [u64] whose first element is 5")
step("Bind it to a second val and read element 0")
expect(_first_via_val_to_val()).to_equal(5)
```

</details>

#### carries values through a val-to-var binding

- carries values through a val-to-var binding
- Bind the same array to a var and read element 0
   - Expected: _first_via_val_to_var() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries values through a val-to-var binding")
step("Bind the same array to a var and read element 0")
expect(_first_via_val_to_var()).to_equal(5)
```

</details>

#### carries values through a var-to-var binding

- carries values through a var-to-var binding
- Bind a var array to another var and read element 0
   - Expected: _first_via_var_to_var() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries values through a var-to-var binding")
step("Bind a var array to another var and read element 0")
expect(_first_via_var_to_var()).to_equal(5)
```

</details>

#### carries values when the source was an array literal

- carries values when the source was an array literal
- Bind a literal-initialised array to a new name and read element 0
   - Expected: _first_via_literal_rebound() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries values when the source was an array literal")
step("Bind a literal-initialised array to a new name and read element 0")
expect(_first_via_literal_rebound()).to_equal(3)
```

</details>

### Length alone does not prove a typed array copied correctly

#### reports the length that the elements should back

- reports the length that the elements should back
- Confirm the copy reports two elements
   - Expected: _length_via_val_to_val() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the length that the elements should back")
# Length survived the defect intact, so a length check is exactly the
# assertion that would have missed it. It is asserted here as context
# for the element checks above, never as a substitute for them.
step("Confirm the copy reports two elements")
expect(_length_via_val_to_val()).to_equal(2)
```

</details>

### The ordinary swap idiom moves values in both directions

#### leaves the second variable holding the first one's value

- leaves the second variable holding the first one's value
- Swap two arrays through a temporary binding
- Read element 0 of the variable that received the original
   - Expected: _swapped_second() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the second variable holding the first one's value")
step("Swap two arrays through a temporary binding")
step("Read element 0 of the variable that received the original")
expect(_swapped_second()).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LANG-ARRAY-BIND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d996d87832ad9739810ca44dfc1991c84e3584a87c6a306203e4ff3750af7e5c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d996d87832ad9739810ca44dfc1991c84e3584a87c6a306203e4ff3750af7e5c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d996d87832ad9739810ca44dfc1991c84e3584a87c6a306203e4ff3750af7e5c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/typed_array_variable_binding_spec.spl
mirror: doc/06_spec/unit/compiler/typed_array_variable_binding_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/typed_array_variable_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/compiler/typed_array_variable_binding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/typed_array_variable_binding_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/compiler/typed_array_variable_binding_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries values through a val-to-val binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/typed_array_variable_binding_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries values through a val-to-var binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/typed_array_variable_binding_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries values through a var-to-var binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
