# Layer-Eq Checker — Real Layout Adapter Spec

> zero_cost_layers_c0_c5_staged_implementation_plan_2026-08-07.md

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer-Eq Checker — Real Layout Adapter Spec

zero_cost_layers_c0_c5_staged_implementation_plan_2026-08-07.md

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Milestone:** M2, doc/03_plan/compiler/forwarding/
zero_cost_layers_c0_c5_staged_implementation_plan_2026-08-07.md

Feeds `src/compiler/35.semantics/layer_eq_checker.spl`'s existing obligation
checks 1-4 (field count, name mapping, per-field type+offset+size, whole-type
size+align) with layouts computed by the REAL compiler type-layout engine
(`src/compiler/30.types/type_layout.spl` -> `_TypeLayout/{layout_core,
arch_and_verify,c_assert_gen}.spl`'s `compute_struct_layout`), not
hand-constructed `LayerEqType`/`LayerEqField` fixture literals like
`layer_eq_checker_spec.spl` uses. This proves `check_layer_eq` discriminates
against the compiler's own computed truth, not just synthetic data someone
might have gotten wrong.

Runs under the Rust seed `bin/simple` (same harness discipline as
`layer_eq_checker_spec.spl`): in-process `use` of both modules, executed via
`bin/simple test`, tree-walk interpreter engine — no JIT/native codegen
involved.

## Scenarios

### layer_eq checker against REAL compiler type_layout

#### accepts two independently-computed real layouts with identical field shape (same-name)

- accepts two independently-computed real layouts with identical field shape (same-name)
   - Expected: v.diagnostic equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts two independently-computed real layouts with identical field shape (same-name)")
val target_fields = [hfield("x", i32_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val view_fields = [hfield("x", i32_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val target = layer_eq_type_from_layout("draw.DeviceRect",
    compute_struct_layout(target_fields, layoutattr_c_repr()), no_renames())
val view = layer_eq_type_from_layout("gui.GuiDeviceRect",
    compute_struct_layout(view_fields, layoutattr_c_repr()), no_renames())
val v = check_layer_eq(view, target)
assert_true(v.ok)
expect(v.diagnostic).to_equal("")
```

</details>

#### accepts a real renamed view (full @layer_field tag set) over real layouts

- accepts a real renamed view (full @layer_field tag set) over real layouts


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a real renamed view (full @layer_field tag set) over real layouts")
val target_fields = [hfield("x", i32_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val view_fields = [hfield("left", i32_t()), hfield("top", i32_t()),
    hfield("extent_x", i32_t()), hfield("extent_y", i32_t())]
val target = layer_eq_type_from_layout("draw.DeviceRect",
    compute_struct_layout(target_fields, layoutattr_c_repr()), no_renames())
val view = layer_eq_type_from_layout("gui.GuiBounds",
    compute_struct_layout(view_fields, layoutattr_c_repr()),
    ["x", "y", "width", "height"])
assert_true(check_layer_eq(view, target).ok)
```

</details>

#### SABOTAGE: rejects a real layout whose field ORDER differs (real offsets diverge)

- SABOTAGE: rejects a real layout whose field ORDER differs (real offsets diverge)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SABOTAGE: rejects a real layout whose field ORDER differs (real offsets diverge)")
val target_fields = [hfield("x", i32_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val view_fields = [hfield("y", i32_t()), hfield("x", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val target = layer_eq_type_from_layout("draw.DeviceRect",
    compute_struct_layout(target_fields, layoutattr_c_repr()), no_renames())
val view = layer_eq_type_from_layout("gui.SwappedRect",
    compute_struct_layout(view_fields, layoutattr_c_repr()), no_renames())
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("error[layer_eq]"))
```

</details>

#### SABOTAGE: rejects a real layout with a widened field type (i64 vs i32 shifts every later offset)

- SABOTAGE: rejects a real layout with a widened field type (i64 vs i32 shifts every later offset)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SABOTAGE: rejects a real layout with a widened field type (i64 vs i32 shifts every later offset)")
val target_fields = [hfield("x", i32_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val view_fields = [hfield("x", i64_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val target = layer_eq_type_from_layout("draw.DeviceRect",
    compute_struct_layout(target_fields, layoutattr_c_repr()), no_renames())
val view = layer_eq_type_from_layout("gui.WidenedRect",
    compute_struct_layout(view_fields, layoutattr_c_repr()), no_renames())
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("error[layer_eq]"))
```

</details>

#### SABOTAGE: rejects a real layout with a same-size field-type swap (f32 vs i32)

- SABOTAGE: rejects a real layout with a same-size field-type swap (f32 vs i32)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SABOTAGE: rejects a real layout with a same-size field-type swap (f32 vs i32)")
val target_fields = [hfield("x", i32_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val view_fields = [hfield("x", f32_t()), hfield("y", i32_t()),
    hfield("width", i32_t()), hfield("height", i32_t())]
val target = layer_eq_type_from_layout("draw.DeviceRect",
    compute_struct_layout(target_fields, layoutattr_c_repr()), no_renames())
val view = layer_eq_type_from_layout("gui.FloatRect",
    compute_struct_layout(view_fields, layoutattr_c_repr()), no_renames())
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("f32"))
```

</details>

#### LOAD-BEARING: rejects a field-order swap where real C-ABI padding changes total size, even though a naive same-fields fixture would have wrongly reported equal size

- LOAD-BEARING: rejects a field-order swap where real C-ABI padding changes total size, even though a naive same-fields fixture would have wrongly reported equal size
   - Expected: target.total_size equals `24`
   - Expected: view.total_size equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LOAD-BEARING: rejects a field-order swap where real C-ABI padding changes total size, even though a naive same-fields fixture would have wrongly reported equal size")
# target: i8, i64, i8 in declared order under C-ABI layout ->
# a@0(1B), pad to 8, b@8(8B), c@16(1B), pad to align(8) -> size 24.
val target_fields = [hfield("a", i8_t()), hfield("b", i64_t()), hfield("c", i8_t())]
# view: same three fields, reordered i8, i8, i64 ->
# a@0(1B), c@1(1B), pad to 8, b@8(8B) -> size 16.
# A hand-written fixture that just sums per-field byte sizes (1+8+1=10
# both sides) or otherwise assumes "same fields => same size" would
# wrongly declare these layout-eq. The REAL compiler layout computes
# genuinely different total sizes (24 vs 16) because of where
# alignment padding lands, and check_layer_eq must reject it.
val view_fields = [hfield("a", i8_t()), hfield("c", i8_t()), hfield("b", i64_t())]
val target = layer_eq_type_from_layout("draw.PaddedTriple",
    compute_struct_layout(target_fields, layoutattr_c_repr()), no_renames())
val view = layer_eq_type_from_layout("gui.ReorderedTriple",
    compute_struct_layout(view_fields, layoutattr_c_repr()), no_renames())
expect(target.total_size).to_equal(24)
expect(view.total_size).to_equal(16)
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("error[layer_eq]"))
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d5b1532f75b68e906867577dff0874e16ebaab35bd2100a1518d20e615b5539`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d5b1532f75b68e906867577dff0874e16ebaab35bd2100a1518d20e615b5539`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d5b1532f75b68e906867577dff0874e16ebaab35bd2100a1518d20e615b5539`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts two independently-computed real layouts with identical field shape (same-name)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a real renamed view (full @layer_field tag set) over real layouts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SABOTAGE: rejects a real layout whose field ORDER differs (real offsets diverge)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
