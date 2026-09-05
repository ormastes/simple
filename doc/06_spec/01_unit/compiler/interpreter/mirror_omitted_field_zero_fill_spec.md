# mirror_omitted_field_zero_fill_spec

> Mirror interpreter: omitted primitive struct fields zero-fill.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mirror_omitted_field_zero_fill_spec

Mirror interpreter: omitted primitive struct fields zero-fill.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirror interpreter: omitted primitive struct fields zero-fill.

Unit-tests struct_field_zero_fill in
src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl —
the self-hosted mirror of the Rust seed's undefaulted_field_fill
(src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs),
whose end-to-end behaviour is pinned by
test/01_unit/compiler/struct_init_field_order_fill_spec.spl.

## Scenarios

### mirror struct_field_zero_fill

#### zero-fills primitive field types and nils the rest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- zero-fills primitive field types and nils the rest
   - Expected: val_get_int(a) equals `0`
   - Expected: val_get_float(b) equals `0.0`
   - Expected: val_get_int(e) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-fills primitive field types and nils the rest")
var names: [text] = ["a", "b", "c", "d", "e"]
var types: [i64] = [TYPE_I64, TYPE_F64, TYPE_BOOL, TYPE_TEXT, TYPE_U32]
var defaults: [i64] = []
var bits: [i64] = []
val d = decl_struct_def("ZeroFillProbe", names, types, defaults, bits, 0)

val a = struct_field_zero_fill(d, 0)
assert_false(val_is_nil(a))
expect(val_get_int(a)).to_equal(0)

val b = struct_field_zero_fill(d, 1)
assert_false(val_is_nil(b))
expect(val_get_float(b)).to_equal(0.0)

val c = struct_field_zero_fill(d, 2)
assert_false(val_is_nil(c))
assert_false(val_get_bool(c))

# text stays nil (reference-ish; matches seed: only int/float/bool zero-fill)
assert_true(val_is_nil(struct_field_zero_fill(d, 3)))

val e = struct_field_zero_fill(d, 4)
assert_false(val_is_nil(e))
expect(val_get_int(e)).to_equal(0)

# out-of-range index is nil, never a crash
assert_true(val_is_nil(struct_field_zero_fill(d, 99)))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `f491452eabc275401c12cefc9222e60a2aa5c50b30be797edaf1a826177bddae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f491452eabc275401c12cefc9222e60a2aa5c50b30be797edaf1a826177bddae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f491452eabc275401c12cefc9222e60a2aa5c50b30be797edaf1a826177bddae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero-fills primitive field types and nils the rest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
