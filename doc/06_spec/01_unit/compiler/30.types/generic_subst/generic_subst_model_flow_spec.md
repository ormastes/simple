# Generic substitution model: every variable-change kind preserves typing

> Contract that every way a generic value moves between places (binding,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic substitution model: every variable-change kind preserves typing

Contract that every way a generic value moves between places (binding,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Contract that every way a generic value moves between places (binding,
assignment, argument, return, field, element, entry, optional, closure,
pattern, loop) keeps its type under substitution. Compiler engineers who
specialize generic bodies read it to know that a body well typed as a
template stays well typed, at the substituted type, in every instance.

## Operator workflow
Run `bin/simple test test/01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl`
after editing `mf_step` or `mf_substitute_inputs`. A failure names the law
(F1 commutes, F2 closed, F3 no invention) and the first offending kind.

## Compatibility and limitations
Covers the 19 kinds of `mf_kinds()` over the bounded flow universe only;
constructors outside it (Result, Ref, Ptr, unions) are not modelled.

## Verification guidance and troubleshooting
The ok/ill case counts per kind are pinned; a changed count means the kind's
typing rule or the universe changed, not that the sweep got faster.
# Generic substitution model: every variable-change kind preserves typing

A generic value changes variable in a fixed number of ways: it is bound by a
`let`, reassigned, passed as an argument, returned, stored into or loaded from
a field, an array element, a dict entry, wrapped in or taken out of an
optional, captured by a closure, called through one, destructured by a
pattern, or bound by a loop. `mf_step` gives the type the destination holds
for each of these 19 kinds.

For every kind this spec enumerates every input tuple of the bounded universe
and, for each well-typed step, every substitution, checking:

- F1 the step is still well typed after substitution, at the substituted
  type (a template body that type-checks keeps type-checking in every
  specialization, and the destination has the specialized type);
- F2 closed inputs give a closed result (no type variable survives into a
  specialization through this kind);
- F3 the result mentions no variable its inputs did not (nothing is invented).

Bounded exhaustive checking, not a proof: 26 types per input slot, 25
substitutions, 19 kinds. Per-kind case counts are printed, and a kind with no
well-typed case fails the spec.

## Scenarios

### generic substitution model: flow universe

#### has the stated sizes

- Run the checks for: has the stated sizes
   - Expected: mf_kinds().len() equals `19)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`
   - Expected: mu_flow_types().len() equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`
   - Expected: flow_substs().len() equals `25)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`
   - Expected: mu_pair_instances().len() equals `25)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`
   - Expected: mu_field_declarations().len() equals `8)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: has the stated sizes")
expect(mf_kinds().len()).to_equal(19)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(mu_flow_types().len()).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(flow_substs().len()).to_equal(25)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(mu_pair_instances().len()).to_equal(25)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(mu_field_declarations().len()).to_equal(8)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

### generic substitution model: bindings keep the type (F1-F3)

#### let with an annotation

- Run the checks for: let with an annotation
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`
   - Expected: ill_cases equals `650)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or t... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: let with an annotation")
sweep_binary(MF_LET)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(ill_cases).to_equal(650)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### let without an annotation

- Run the checks for: let without an annotation
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: let without an annotation")
sweep_unary(MF_LET_INFER)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### assignment to a var

- Run the checks for: assignment to a var
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: assignment to a var")
sweep_binary(MF_ASSIGN)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### argument passed to a parameter

- Run the checks for: argument passed to a parameter
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: argument passed to a parameter")
sweep_binary(MF_PARAM)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### value returned

- Run the checks for: value returned
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: value returned")
sweep_binary(MF_RETURN)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### closure capture

- Run the checks for: closure capture
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: closure capture")
sweep_unary(MF_CAPTURE)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

### generic substitution model: containers keep the element type (F1-F3)

#### array element read

- Run the checks for: array element read
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`
   - Expected: ill_cases equals `21)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: array element read")
sweep_unary(MF_ELEM_READ)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(ill_cases).to_equal(21)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### array element write

- Run the checks for: array element write
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: array element write")
sweep_binary(MF_ELEM_WRITE)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

<details>
<summary>Advanced: loop variable</summary>

#### loop variable

- Run the checks for: loop variable
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: loop variable")
sweep_unary(MF_LOOP)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>


</details>

#### dict entry read

- Run the checks for: dict entry read
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: dict entry read")
sweep_binary(MF_DICT_READ)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### dict entry write

- Run the checks for: dict entry write
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`
   - Expected: ok_cases + ill_cases equals `17576)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: dict entry write")
reset()
val substs = flow_substs()
val types = mu_flow_types()
for a in types:
    val x: MType = a
    for b in types:
        val y: MType = b
        # Only a key of the dict's key type can be well typed; the
        # value slot is still swept over every type.
        if mf_is_ok(mf_step(MF_DICT_READ, [x, y], [])):
            for c in types:
                val z: MType = c
                check_case(MF_DICT_WRITE, [x, y, z], [], substs)
        else:
            skip_ill(types.len())
print "dict_write: ok={ok_cases} ill={ill_cases} substituted={substituted}"
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(ok_cases + ill_cases).to_equal(17576)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### tuple destructuring, both components

- Run the checks for: tuple destructuring, both components
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: tuple destructuring, both components")
sweep_unary(MF_TUPLE_FIRST)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
sweep_unary(MF_TUPLE_SECOND)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

### generic substitution model: optionals and closures (F1-F3)

#### wrap into an optional

- Run the checks for: wrap into an optional
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: wrap into an optional")
sweep_unary(MF_OPT_WRAP)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### unwrap / payload pattern

- Run the checks for: unwrap / payload pattern
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: unwrap / payload pattern")
sweep_unary(MF_OPT_UNWRAP)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### coalesce with a default

- Run the checks for: coalesce with a default
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: coalesce with a default")
sweep_binary(MF_OPT_DEFAULT)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

#### call through a closure value

- Run the checks for: call through a closure value
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tru... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: call through a closure value")
sweep_binary(MF_CLOSURE_CALL)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

### generic substitution model: generic struct fields (F1-F3)

#### field read instantiates the declaration by the instance's arguments

- Run the checks for: field read instantiates the declaration by the instance's arguments
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `175)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or t... (full value in folded executable source)`
   - Expected: ill_cases equals `25)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or tr... (full value in folded executable source)`
   - Expected: mf_render(read) equals `Ok(Array<'T>)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: field read instantiates the declaration by the instance's arguments")
reset()
val substs = flow_substs()
for inst in mu_pair_instances():
    val it_: MType = inst
    for d in mu_field_declarations():
        val dt: MType = d
        check_case(MF_FIELD_READ, [it_, dt], ["P", "Q"], substs)
print "field_read: ok={ok_cases} ill={ill_cases} substituted={substituted}"
expect(first_bad).to_equal("")
# 25 instances x 7 declarations closed over P, Q; the eighth is open.
expect(ok_cases).to_equal(175)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(ill_cases).to_equal(25)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
val read = mf_step(MF_FIELD_READ, [mt_app(MU_PAIR, [mt_var("T"), mt_con("i64")]), mt_app(MT_ARRAY, [mt_var("P")])], ["P", "Q"])
expect(mf_render(read)).to_equal("Ok(Array<'T>)")
```

</details>

#### a declaration open in a variable of the enclosing function is rejected

- Run the checks for: a declaration open in a variable of the enclosing function is rejected
   - Expected: mf_render(open) equals `Ill(open_declaration)`
   - Expected: mf_render(wrong_arity) equals `Ill(shape)`
   - Expected: mf_render(not_an_instance) equals `Ill(shape)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: a declaration open in a variable of the enclosing function is rejected")
val open = mf_step(MF_FIELD_READ, [mt_app(MU_PAIR, [mt_con("i64"), mt_con("i64")]), mt_var("T")], ["P", "Q"])
expect(mf_render(open)).to_equal("Ill(open_declaration)")
val wrong_arity = mf_step(MF_FIELD_READ, [mt_app(MU_BOX, [mt_con("i64")]), mt_var("P")], ["P", "Q"])
expect(mf_render(wrong_arity)).to_equal("Ill(shape)")
val not_an_instance = mf_step(MF_FIELD_READ, [mt_app(MT_ARRAY, [mt_con("i64")]), mt_var("P")], ["P"])
expect(mf_render(not_an_instance)).to_equal("Ill(shape)")
```

</details>

#### field write accepts exactly the instantiated field type

- Run the checks for: field write accepts exactly the instantiated field type
   - Expected: first_bad equals ``
   - Expected: ok_cases > 0 is true
   - Expected: ok_cases + ill_cases equals `5200)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-005
step("Run the checks for: field write accepts exactly the instantiated field type")
reset()
val substs = flow_substs()
val values = mu_flow_types()
for inst in mu_pair_instances():
    val it_: MType = inst
    for d in mu_field_declarations():
        val dt: MType = d
        for v in values:
            val vt: MType = v
            check_case(MF_FIELD_WRITE, [it_, dt, vt], ["P", "Q"], substs)
print "field_write: ok={ok_cases} ill={ill_cases} substituted={substituted}"
expect(first_bad).to_equal("")
expect(ok_cases > 0).to_equal(true)
expect(ok_cases + ill_cases).to_equal(5200)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GSUBST-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6cdcc298224078946a2e60b9315fee9f5d464ceff96046de5c95e2670628fc94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6cdcc298224078946a2e60b9315fee9f5d464ceff96046de5c95e2670628fc94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6cdcc298224078946a2e60b9315fee9f5d464ceff96046de5c95e2670628fc94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: 01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl
mirror: doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has the stated sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'let with an annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'let without an annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
