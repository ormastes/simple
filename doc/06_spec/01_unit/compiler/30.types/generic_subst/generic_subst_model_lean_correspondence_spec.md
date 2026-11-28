# Generic substitution model: Lean-only laws, key parity, template instantiation

> Contract for the parts of the substitution model that the laws and flow specs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic substitution model: Lean-only laws, key parity, template instantiation

Contract for the parts of the substitution model that the laws and flow specs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Contract for the parts of the substitution model that the laws and flow specs
do not cover: the Lean-only theorems of `GenericSubstModel.lean`, byte-equality
of the model key with the text the template projector writes, template
instantiation for the TLDR generic view, and the boundary behaviour of
matching, inference, flow steps and key decoding. Compiler engineers wiring
the instance task or the TLDR view read it to learn the exact classification
(closed, open, depth, malformed) they will receive.

## Operator workflow
Run `bin/simple test test/01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.spl`
after editing the model, the projector key helpers, or the Lean file.

## Compatibility and limitations
The projector parity cases use closed types only (a binder id embeds the
declaration symbol). Lean proves substitution laws; the key and flow laws are
bounded sweeps in the sibling specs.

## Verification guidance and troubleshooting
A parity failure means `mt_key_type` and the projector's `_key_*` helpers
diverged; fix whichever changed last and rerun the TLDR view specs.
# Generic substitution model: Lean-only laws, key parity, template instantiation

Checks the Lean theorems of `GenericSubstModel.lean` that the laws spec does not
already cover (the correspondence table is the header of
`generic_subst_model.spl`), the equality of `mt_key_type` with the text the
template projector writes, and `mt_instantiate_key` (the TLDR view acquirer's
entry point). Sweeps assert their sizes so an empty sweep fails.

## Scenarios

### generic substitution model: Lean-only laws

#### S0 the empty substitution is the identity

- Run the checks for: S0 the empty substitution is the identity
   - Expected: n equals `365)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or t... (full value in folded executable source)`
   - Expected: bad equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Run the checks for: S0 the empty substitution is the identity")
var n = 0
var bad = ""
for t in mu_types():
    val tt: MType = t
    n = n + 1
    if not mt_struct_eq(ms_apply(ms_empty(), tt), tt):
        bad = mt_render(tt)
expect(n).to_equal(365)  # oracle: pinned size of the exhaustive sweep or fixture; an empty or truncated sweep changes it
expect(bad).to_equal("")
```

</details>

#### unknown is never closed and no substitution moves it

- Run the checks for: unknown is never closed and no substitution moves it
   - Expected: mt_is_closed(mt_unknown()) is false
   - Expected: mt_is_unknown(mt_unknown()) is true
   - Expected: mt_is_unknown(int_t()) is false
   - Expected: mt_is_unknown(mt_var("T")) is false
   - Expected: mt_is_closed(mt_app(MT_TUPLE, [mt_unknown()])) is false
   - Expected: mt_is_closed(mt_app(MT_TUPLE, [int_t(), text_t()])) is true
   - Expected: mt_is_unknown(ms_apply(s, mt_unknown())) is true
   - Expected: mt_is_unknown(ms_apply(ms_empty(), mt_unknown())) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Run the checks for: unknown is never closed and no substitution moves it")
expect(mt_is_closed(mt_unknown())).to_equal(false)
expect(mt_is_unknown(mt_unknown())).to_equal(true)
expect(mt_is_unknown(int_t())).to_equal(false)
expect(mt_is_unknown(mt_var("T"))).to_equal(false)
expect(mt_is_closed(mt_app(MT_TUPLE, [mt_unknown()]))).to_equal(false)
expect(mt_is_closed(mt_app(MT_TUPLE, [int_t(), text_t()]))).to_equal(true)
val s = ms_bind(ms_bind(ms_empty(), "T", int_t()), "U", text_t())
expect(mt_is_unknown(ms_apply(s, mt_unknown()))).to_equal(true)
expect(mt_is_unknown(ms_apply(ms_empty(), mt_unknown()))).to_equal(true)
```

</details>

#### an application keeps its constructor and arity

- Run the checks for: an application keeps its constructor and arity
   - Expected: apps > 0 is true
   - Expected: bad equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Run the checks for: an application keeps its constructor and arity")
var apps = 0
var bad = ""
val s = ms_bind(ms_bind(ms_empty(), "T", int_t()), "U", mt_app(MT_ARRAY, [text_t()]))
for t in mu_types():
    val tt: MType = t
    match tt:
        case MType.App(c, args):
            apps = apps + 1
            match ms_apply(s, tt):
                case MType.App(c2, args2):
                    if c2 != c or args2.len() != args.len():
                        bad = mt_render(tt)
                case _:
                    bad = mt_render(tt)
        case _:
            bad = bad
expect(apps > 0).to_equal(true)
expect(bad).to_equal("")
```

</details>

#### an open range is not idempotent (ClosedRange is needed)

- Run the checks for: an open range is not idempotent (ClosedRange is needed)
   - Expected: ms_range_closed(chain) is false
   - Expected: mt_struct_eq(once, twice) is false
   - Expected: mt_render(twice) equals `i64`
   - Expected: ms_range_closed(closed) is true
   - Expected: ms_range_closed(ms_empty()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Run the checks for: an open range is not idempotent (ClosedRange is needed)")
val chain = ms_bind(ms_bind(ms_empty(), "T", mt_var("U")), "U", int_t())
expect(ms_range_closed(chain)).to_equal(false)
val once = ms_apply(chain, mt_var("T"))
val twice = ms_apply(chain, once)
expect(mt_struct_eq(once, twice)).to_equal(false)
expect(mt_render(twice)).to_equal("i64")
val closed = ms_bind(ms_empty(), "T", int_t())
expect(ms_range_closed(closed)).to_equal(true)
expect(ms_range_closed(ms_empty())).to_equal(true)
```

</details>

#### ms_get answers unknown for an unbound name

- Run the checks for: ms_get answers unknown for an unbound name
   - Expected: ms_has(s, "T") is true
   - Expected: ms_has(s, "U") is false
   - Expected: mt_struct_eq(ms_get(s, "T"), int_t()) is true
   - Expected: mt_is_unknown(ms_get(s, "U")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Run the checks for: ms_get answers unknown for an unbound name")
val s = ms_bind(ms_empty(), "T", int_t())
expect(ms_has(s, "T")).to_equal(true)
expect(ms_has(s, "U")).to_equal(false)
expect(mt_struct_eq(ms_get(s, "T"), int_t())).to_equal(true)
expect(mt_is_unknown(ms_get(s, "U"))).to_equal(true)
```

</details>

#### rendering is readable and order independent

- Run the checks for: rendering is readable and order independent
   - Expected: mt_render(t) equals `Dict<'K,Array<i64>>`
   - Expected: mt_render_list([int_t(), mt_var("T")]) equals `[i64,'T]`
   - Expected: ms_render(a) equals `ms_render(b)`
   - Expected: mm_render(MMatch.Conflict("T")) equals `Conflict(T)`
   - Expected: mm_render(MMatch.Shape) equals `Shape`
   - Expected: mm_is_bound(MMatch.Shape) is false
   - Expected: mm_is_bound(MMatch.Bound(a)) is true
   - Expected: ms_domain(mm_subst(MMatch.Shape)).len() equals `0)  # oracle: a non-Bound match carries the empty substitution; the Bound cas... (full value in folded executable source)`
   - Expected: ms_domain(mm_subst(MMatch.Bound(a))).len() equals `2)  # oracle: a non-Bound match carries the empty substitution; the Bound cas... (full value in folded executable source)`
   - Expected: mi_render(MInfer.Unresolved(MI_NO_EVIDENCE)) equals `Unresolved(no_evidence)`
   - Expected: mi_render(MInfer.Resolved([int_t()])) equals `Resolved[i64]`
   - Expected: mi_is_resolved(MInfer.Resolved([])) is true
   - Expected: mi_is_resolved(MInfer.Unresolved(MI_SHAPE)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Run the checks for: rendering is readable and order independent")
val t = mt_app(MT_DICT, [mt_var("K"), mt_app(MT_ARRAY, [int_t()])])
expect(mt_render(t)).to_equal("Dict<'K,Array<i64>>")
expect(mt_render_list([int_t(), mt_var("T")])).to_equal("[i64,'T]")
val a = ms_bind(ms_bind(ms_empty(), "B", int_t()), "A", text_t())
val b = ms_bind(ms_bind(ms_empty(), "A", text_t()), "B", int_t())
expect(ms_render(a)).to_equal(ms_render(b))
expect(mm_render(MMatch.Conflict("T"))).to_equal("Conflict(T)")
expect(mm_render(MMatch.Shape)).to_equal("Shape")
expect(mm_is_bound(MMatch.Shape)).to_equal(false)
expect(mm_is_bound(MMatch.Bound(a))).to_equal(true)
expect(ms_domain(mm_subst(MMatch.Shape)).len()).to_equal(0)  # oracle: a non-Bound match carries the empty substitution; the Bound case binds the two names A and B
expect(ms_domain(mm_subst(MMatch.Bound(a))).len()).to_equal(2)  # oracle: a non-Bound match carries the empty substitution; the Bound case binds the two names A and B
expect(mi_render(MInfer.Unresolved(MI_NO_EVIDENCE))).to_equal("Unresolved(no_evidence)")
expect(mi_render(MInfer.Resolved([int_t()]))).to_equal("Resolved[i64]")
expect(mi_is_resolved(MInfer.Resolved([]))).to_equal(true)
expect(mi_is_resolved(MInfer.Unresolved(MI_SHAPE))).to_equal(false)
```

</details>

### generic substitution model: key parity with the projector

#### mt_key_type equals the projector key text

- Run the checks for: mt_key_type equals the projector key text
   - Expected: cases.len() equals `expect_types.len()`
   - Expected: k.is_ok() is true
   - Expected: k.unwrap() equals `mt_key_type(expect_types[i])`
   - Expected: checked equals `10)  # oracle: one projector comparison per listed type text (10 texts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Run the checks for: mt_key_type equals the projector key text")
val d = probe_decl()
val cases: [text] = ["i64", "text", "bool", "Array<i64>", "[text]", "Optional<bool>", "i64?",
    "Dict<text, i64>", "Pkg.Box<i64>", "Box<[text]>"]
val expect_types: [MType] = [
    int_t(), text_t(), mt_con("bool"),
    mt_app(MT_ARRAY, [int_t()]), mt_app(MT_ARRAY, [text_t()]),
    mt_app(MT_OPTIONAL, [mt_con("bool")]), mt_app(MT_OPTIONAL, [int_t()]),
    mt_app(MT_DICT, [text_t(), int_t()]),
    mt_app("Named:Pkg.Box", [int_t()]), mt_app("Named:pkg.Box", [mt_app(MT_ARRAY, [text_t()])])]
expect(cases.len()).to_equal(expect_types.len())
var i = 0
var checked = 0
while i < cases.len():
    val k = generic_type_text_key_v1(d, cases[i])
    expect(k.is_ok()).to_equal(true)
    expect(k.unwrap()).to_equal(mt_key_type(expect_types[i]))
    checked = checked + 1
    i = i + 1
expect(checked).to_equal(10)  # oracle: one projector comparison per listed type text (10 texts)
```

</details>

### generic substitution model: template instantiation

#### substitutes positional binders and classifies the result closed

- Run the checks for: substitutes positional binders and classifies the result closed
   - Expected: r.status equals `MI_STATUS_CLOSED`
   - Expected: mt_render(r.t) equals `Array<i64>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-006
step("Run the checks for: substitutes positional binders and classifies the result closed")
val key = mt_key_type(mt_app(MT_ARRAY, [mt_var("pkg.Box#0")]))
val r = mt_instantiate_key(key, ["pkg.Box#0"], [int_t()], 8)
expect(r.status).to_equal(MI_STATUS_CLOSED)
expect(mt_render(r.t)).to_equal("Array<i64>")
```

</details>

#### reports open when a binder has no argument

- Run the checks for: reports open when a binder has no argument
   - Expected: r.status equals `MI_STATUS_OPEN`
   - Expected: mt_render(r.t) equals `Tuple<i64,'a#1>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-006
step("Run the checks for: reports open when a binder has no argument")
val key = mt_key_type(mt_app(MT_TUPLE, [mt_var("a#0"), mt_var("a#1")]))
val r = mt_instantiate_key(key, ["a#0", "a#1"], [int_t()], 8)
expect(r.status).to_equal(MI_STATUS_OPEN)
expect(mt_render(r.t)).to_equal("Tuple<i64,'a#1>")
```

</details>

#### reports depth when the result nests deeper than the limit

- Run the checks for: reports depth when the result nests deeper than the limit
   - Expected: deep.status equals `MI_STATUS_DEPTH`
   - Expected: fits.status equals `MI_STATUS_CLOSED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-006
step("Run the checks for: reports depth when the result nests deeper than the limit")
val key = mt_key_type(mt_app(MT_ARRAY, [mt_app(MT_ARRAY, [mt_var("a#0")])]))
val deep = mt_instantiate_key(key, ["a#0"], [mt_app(MT_ARRAY, [int_t()])], 2)
expect(deep.status).to_equal(MI_STATUS_DEPTH)
val fits = mt_instantiate_key(key, ["a#0"], [mt_app(MT_ARRAY, [int_t()])], 3)
expect(fits.status).to_equal(MI_STATUS_CLOSED)
```

</details>

#### reports malformed for undecodable key text

- Run the checks for: reports malformed for undecodable key text
   - Expected: r.status equals `MI_STATUS_MALFORMED`
   - Expected: mt_is_unknown(r.t) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Run the checks for: reports malformed for undecodable key text")
val r = mt_instantiate_key("zz", ["a#0"], [int_t()], 8)
expect(r.status).to_equal(MI_STATUS_MALFORMED)
expect(mt_is_unknown(r.t)).to_equal(true)
```

</details>

#### ms_from_positional ignores surplus binders and surplus arguments

- Run the checks for: ms_from_positional ignores surplus binders and surplus arguments
   - Expected: ms_has(short_args, "A") is true
   - Expected: ms_has(short_args, "B") is false
   - Expected: ms_domain(short_binders).len() equals `1)  # oracle: only the one supplied binder A is bound; the surplus argument i... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-006
step("Run the checks for: ms_from_positional ignores surplus binders and surplus arguments")
val short_args = ms_from_positional(["A", "B"], [int_t()])
expect(ms_has(short_args, "A")).to_equal(true)
expect(ms_has(short_args, "B")).to_equal(false)
val short_binders = ms_from_positional(["A"], [int_t(), text_t()])
expect(ms_domain(short_binders).len()).to_equal(1)  # oracle: only the one supplied binder A is bound; the surplus argument is dropped
```

</details>

### generic substitution model: boundary behaviour

#### matching a slice pattern accepts an array and refuses another constructor

- Run the checks for: matching a slice pattern accepts an array and refuses another constructor
   - Expected: mm_render(over_array) equals `Bound\{T:=i64}`
   - Expected: mm_render(over_optional) equals `Shape`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Run the checks for: matching a slice pattern accepts an array and refuses another constructor")
val slice_t = mt_app("Slice", [mt_var("T")])
val over_array = mm_match(slice_t, mt_app(MT_ARRAY, [int_t()]), ms_empty())
expect(mm_render(over_array)).to_equal("Bound\{T:=i64}")
val over_optional = mm_match(slice_t, mt_app(MT_OPTIONAL, [int_t()]), ms_empty())
expect(mm_render(over_optional)).to_equal("Shape")
```

</details>

#### matching refuses the same constructor at a different arity

- Run the checks for: matching refuses the same constructor at a different arity
   - Expected: mm_render(mm_match(pattern, evidence, ms_empty())) equals `Shape`
   - Expected: mt_struct_eq(pattern, evidence) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Run the checks for: matching refuses the same constructor at a different arity")
val pattern = mt_app(MT_TUPLE, [mt_var("T")])
val evidence = mt_app(MT_TUPLE, [int_t(), int_t()])
expect(mm_render(mm_match(pattern, evidence, ms_empty()))).to_equal("Shape")
expect(mt_struct_eq(pattern, evidence)).to_equal(false)
```

</details>

#### call-site inference tolerates missing arguments and an open expected type

- Run the checks for: call-site inference tolerates missing arguments and an open expected type
   - Expected: mi_render(missing_arg) equals `Unresolved(no_evidence)`
   - Expected: mi_render(open_expected) equals `Unresolved(no_evidence)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Run the checks for: call-site inference tolerates missing arguments and an open expected type")
val missing_arg = mi_infer(["T", "U"], [mt_var("T"), mt_var("U")], int_t(), [], [int_t()], mt_unknown(), false)
expect(mi_render(missing_arg)).to_equal("Unresolved(no_evidence)")
val open_expected = mi_infer(["T"], [], mt_var("T"), [], [], mt_var("U"), false)
expect(mi_render(open_expected)).to_equal("Unresolved(no_evidence)")
```

</details>

#### a step with the wrong number of inputs, or an unknown kind, is ill typed

- Run the checks for: a step with the wrong number of inputs, or an unknown kind, is ill typed
   - Expected: mf_render(mf_step("let", [int_t()], [])) equals `Ill(arity)`
   - Expected: mf_render(mf_step("no_such_kind", [int_t(), int_t()], [])) equals `Ill(unknown_kind)`
   - Expected: mf_render(mf_step("elem_read", [mt_app(MT_ARRAY, [int_t(), int_t()])], [])) equals `Ill(shape)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Run the checks for: a step with the wrong number of inputs, or an unknown kind, is ill typed")
expect(mf_render(mf_step("let", [int_t()], []))).to_equal("Ill(arity)")
expect(mf_render(mf_step("no_such_kind", [int_t(), int_t()], []))).to_equal("Ill(unknown_kind)")
expect(mf_render(mf_step("elem_read", [mt_app(MT_ARRAY, [int_t(), int_t()])], []))).to_equal("Ill(shape)")
```

</details>

#### a dict write checks the container shape and the key type

- Run the checks for: a dict write checks the container shape and the key type
   - Expected: mf_render(mf_step("dict_write", [dict_t, text_t(), int_t()], [])) equals `Ok(i64)`
   - Expected: mf_render(mf_step("dict_write", [int_t(), text_t(), int_t()], [])) equals `Ill(shape)`
   - Expected: mf_render(mf_step("dict_write", [dict_t, int_t(), int_t()], [])) equals `Ill(mismatch)`
   - Expected: mf_render(mf_step("dict_write", [dict_t, text_t(), text_t()], [])) equals `Ill(mismatch)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Run the checks for: a dict write checks the container shape and the key type")
val dict_t = mt_app(MT_DICT, [text_t(), int_t()])
expect(mf_render(mf_step("dict_write", [dict_t, text_t(), int_t()], []))).to_equal("Ok(i64)")
expect(mf_render(mf_step("dict_write", [int_t(), text_t(), int_t()], []))).to_equal("Ill(shape)")
expect(mf_render(mf_step("dict_write", [dict_t, int_t(), int_t()], []))).to_equal("Ill(mismatch)")
expect(mf_render(mf_step("dict_write", [dict_t, text_t(), text_t()], []))).to_equal("Ill(mismatch)")
```

</details>

#### key decoding refuses every malformed spelling

- Run the checks for: key decoding refuses every malformed spelling
   - Expected: refused equals `bad_keys.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-004
step("Run the checks for: key decoding refuses every malformed spelling")
val bad_keys: [text] = ["c5", "c:", "cx:", "c/:", "c1234567890123:x", "x1:a", "a1:X", "a1:Xz", "a1:Xlz:", "a1:Xl2:c1:a", ""]
var refused = 0
for k in bad_keys:
    val kk: text = k
    if not mt_from_key(kk).ok:
        refused = refused + 1
expect(refused).to_equal(bad_keys.len())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GSUBST-004`
- `REQ-GSUBST-001`
- `REQ-GSUBST-006`
- `REQ-GSUBST-002`
- `REQ-GSUBST-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ad11742492a0ba356cb9487491c1a42b8edd8ef8733a6ca3bb976e862f3b15c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ad11742492a0ba356cb9487491c1a42b8edd8ef8733a6ca3bb976e862f3b15c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ad11742492a0ba356cb9487491c1a42b8edd8ef8733a6ca3bb976e862f3b15c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: 01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.spl
mirror: doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'S0 the empty substitution is the identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unknown is never closed and no substitution moves it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an application keeps its constructor and arity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_lean_correspondence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
