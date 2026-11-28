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

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Build the flow universes (kinds, types, substitutions, instances, declarations) and count them
   - Expected: mf_kinds().len() equals `19)  # oracle: one per variable-change kind listed in mf_kinds(`
   - Expected: mu_flow_types().len() equals `26)  # oracle: size of mu_flow_types(), the bounded flow universe`
   - Expected: flow_substs().len() equals `25)  # oracle: two variables bound or not over the 5 atoms: 5 x 5`
   - Expected: mu_pair_instances().len() equals `25)  # oracle: Pair<A,B> over 5 atoms for each argument: 5 x 5`
   - Expected: mu_field_declarations().len() equals `8)  # oracle: the 8 declared field types of the universe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Build the flow universes (kinds, types, substitutions, instances, declarations) and count them")
expect(mf_kinds().len()).to_equal(19)  # oracle: one per variable-change kind listed in mf_kinds()
expect(mu_flow_types().len()).to_equal(26)  # oracle: size of mu_flow_types(), the bounded flow universe
expect(flow_substs().len()).to_equal(25)  # oracle: two variables bound or not over the 5 atoms: 5 x 5
expect(mu_pair_instances().len()).to_equal(25)  # oracle: Pair<A,B> over 5 atoms for each argument: 5 x 5
expect(mu_field_declarations().len()).to_equal(8)  # oracle: the 8 declared field types of the universe
```

</details>

### generic substitution model: bindings keep the type (F1-F3)

#### let with an annotation

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'let with an annotation' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: each of the 26 flow types is accepted once (the destination eq... (full value in folded executable source)`
   - Expected: ill_cases equals `650)  # oracle: 676 ordered pairs of the 26 flow types minus the 26 pairs who... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'let with an annotation' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_LET)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: each of the 26 flow types is accepted once (the destination equals the value, or the kind passes its input on)
expect(ill_cases).to_equal(650)  # oracle: 676 ordered pairs of the 26 flow types minus the 26 pairs whose types agree
```

</details>

#### let without an annotation

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'let without an annotation' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: each of the 26 flow types is accepted once (the destination eq... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'let without an annotation' kind through mf_step and its substituted copy, then compare")
sweep_unary(MF_LET_INFER)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: each of the 26 flow types is accepted once (the destination equals the value, or the kind passes its input on)
```

</details>

#### assignment to a var

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'assignment to a var' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: each of the 26 flow types is accepted once (the destination eq... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'assignment to a var' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_ASSIGN)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: each of the 26 flow types is accepted once (the destination equals the value, or the kind passes its input on)
```

</details>

#### argument passed to a parameter

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'argument passed to a parameter' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: each of the 26 flow types is accepted once (the destination eq... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'argument passed to a parameter' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_PARAM)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: each of the 26 flow types is accepted once (the destination equals the value, or the kind passes its input on)
```

</details>

#### value returned

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'value returned' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: each of the 26 flow types is accepted once (the destination eq... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'value returned' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_RETURN)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: each of the 26 flow types is accepted once (the destination equals the value, or the kind passes its input on)
```

</details>

#### closure capture

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'closure capture' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: each of the 26 flow types is accepted once (the destination eq... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'closure capture' kind through mf_step and its substituted copy, then compare")
sweep_unary(MF_CAPTURE)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: each of the 26 flow types is accepted once (the destination equals the value, or the kind passes its input on)
```

</details>

### generic substitution model: containers keep the element type (F1-F3)

#### array element read

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'array element read' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: 5 of the 26 flow types are arrays, the only container this kind... (full value in folded executable source)`
   - Expected: ill_cases equals `21)  # oracle: the 26 - 5 flow types that are not arrays are refused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'array element read' kind through mf_step and its substituted copy, then compare")
sweep_unary(MF_ELEM_READ)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: 5 of the 26 flow types are arrays, the only container this kind accepts
expect(ill_cases).to_equal(21)  # oracle: the 26 - 5 flow types that are not arrays are refused
```

</details>

#### array element write

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'array element write' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: 5 of the 26 flow types are arrays, the only container this kind... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'array element write' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_ELEM_WRITE)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: 5 of the 26 flow types are arrays, the only container this kind accepts
```

</details>

<details>
<summary>Advanced: loop variable</summary>

#### loop variable

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'loop variable' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: 5 of the 26 flow types are arrays, the only container this kind... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'loop variable' kind through mf_step and its substituted copy, then compare")
sweep_unary(MF_LOOP)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: 5 of the 26 flow types are arrays, the only container this kind accepts
```

</details>


</details>

#### dict entry read

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'dict entry read' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: only the two-argument constructor types of this kind (2 of the ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'dict entry read' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_DICT_READ)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: only the two-argument constructor types of this kind (2 of the 26 flow types) are accepted
```

</details>

#### dict entry write

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'dict entry write' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: only the two-argument constructor types of this kind (2 of the ... (full value in folded executable source)`
   - Expected: ok_cases + ill_cases equals `17576)  # oracle: 26 x 26 x 26 ordered triples of flow types`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'dict entry write' kind through mf_step and its substituted copy, then compare")
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
expect(ok_cases).to_equal(2)  # oracle: only the two-argument constructor types of this kind (2 of the 26 flow types) are accepted
expect(ok_cases + ill_cases).to_equal(17576)  # oracle: 26 x 26 x 26 ordered triples of flow types
```

</details>

#### tuple destructuring, both components

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'tuple destructuring, both components' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: only the two-argument constructor types of this kind (2 of the ... (full value in folded executable source)`
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: only the two-argument constructor types of this kind (2 of the ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'tuple destructuring, both components' kind through mf_step and its substituted copy, then compare")
sweep_unary(MF_TUPLE_FIRST)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: only the two-argument constructor types of this kind (2 of the 26 flow types) are accepted
sweep_unary(MF_TUPLE_SECOND)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: only the two-argument constructor types of this kind (2 of the 26 flow types) are accepted
```

</details>

### generic substitution model: optionals and closures (F1-F3)

#### wrap into an optional

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'wrap into an optional' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `26)  # oracle: each of the 26 flow types is accepted once (the destination eq... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'wrap into an optional' kind through mf_step and its substituted copy, then compare")
sweep_unary(MF_OPT_WRAP)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(26)  # oracle: each of the 26 flow types is accepted once (the destination equals the value, or the kind passes its input on)
```

</details>

#### unwrap / payload pattern

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'unwrap / payload pattern' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: 5 of the 26 flow types are optionals, the only type this kind a... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'unwrap / payload pattern' kind through mf_step and its substituted copy, then compare")
sweep_unary(MF_OPT_UNWRAP)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: 5 of the 26 flow types are optionals, the only type this kind accepts
```

</details>

#### coalesce with a default

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'coalesce with a default' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `5)  # oracle: 5 of the 26 flow types are optionals, the only type this kind a... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'coalesce with a default' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_OPT_DEFAULT)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(5)  # oracle: 5 of the 26 flow types are optionals, the only type this kind accepts
```

</details>

#### call through a closure value

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Step every input of the 'call through a closure value' kind through mf_step and its substituted copy, then compare
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `2)  # oracle: only the two-argument constructor types of this kind (2 of the ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Step every input of the 'call through a closure value' kind through mf_step and its substituted copy, then compare")
sweep_binary(MF_CLOSURE_CALL)
expect(first_bad).to_equal("")
expect(ok_cases).to_equal(2)  # oracle: only the two-argument constructor types of this kind (2 of the 26 flow types) are accepted
```

</details>

### generic substitution model: generic struct fields (F1-F3)

#### field read instantiates the declaration by the instance's arguments

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Read every declaration of the universe through every Pair instance and compare with substitution
   - Expected: first_bad equals ``
   - Expected: ok_cases equals `175)  # oracle: of the 8 x 25 = 200 declaration x instance pairs, 175 are acc... (full value in folded executable source)`
   - Expected: ill_cases equals `25)  # oracle: the remaining 25 of the 200 pairs are shape errors`
   - Expected: mf_render(read) equals `Ok(Array<'T>)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Read every declaration of the universe through every Pair instance and compare with substitution")
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
expect(ok_cases).to_equal(175)  # oracle: of the 8 x 25 = 200 declaration x instance pairs, 175 are accepted
expect(ill_cases).to_equal(25)  # oracle: the remaining 25 of the 200 pairs are shape errors
val read = mf_step(MF_FIELD_READ, [mt_app(MU_PAIR, [mt_var("T"), mt_con("i64")]), mt_app(MT_ARRAY, [mt_var("P")])], ["P", "Q"])
expect(mf_render(read)).to_equal("Ok(Array<'T>)")
```

</details>

#### a declaration open in a variable of the enclosing function is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Read a field through three hand-picked invalid instances: open declaration, wrong arity, not an instance
   - Expected: mf_render(open) equals `Ill(open_declaration)`
   - Expected: mf_render(wrong_arity) equals `Ill(shape)`
   - Expected: mf_render(not_an_instance) equals `Ill(shape)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Read a field through three hand-picked invalid instances: open declaration, wrong arity, not an instance")
val open = mf_step(MF_FIELD_READ, [mt_app(MU_PAIR, [mt_con("i64"), mt_con("i64")]), mt_var("T")], ["P", "Q"])
expect(mf_render(open)).to_equal("Ill(open_declaration)")
val wrong_arity = mf_step(MF_FIELD_READ, [mt_app(MU_BOX, [mt_con("i64")]), mt_var("P")], ["P", "Q"])
expect(mf_render(wrong_arity)).to_equal("Ill(shape)")
val not_an_instance = mf_step(MF_FIELD_READ, [mt_app(MT_ARRAY, [mt_con("i64")]), mt_var("P")], ["P"])
expect(mf_render(not_an_instance)).to_equal("Ill(shape)")
```

</details>

#### field write accepts exactly the instantiated field type

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Write a field of every instance with every value type and compare with the instantiated field type
   - Expected: first_bad equals ``
   - Expected: ok_cases > 0 is true
   - Expected: ok_cases + ill_cases equals `5200)  # oracle: 200 declaration x instance pairs x 26 value types`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Write a field of every instance with every value type and compare with the instantiated field type")
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
expect(ok_cases + ill_cases).to_equal(5200)  # oracle: 200 declaration x instance pairs x 26 value types
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

- `REQ-GSUBST-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b29f101a357b86727b48a17e857078a224d75877264dd9a2b99e4230ff02e730`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b29f101a357b86727b48a17e857078a224d75877264dd9a2b99e4230ff02e730`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b29f101a357b86727b48a17e857078a224d75877264dd9a2b99e4230ff02e730`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: 01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.spl
mirror: doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
