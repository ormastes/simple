# hir_types_equal_int_width_spec

> Regression: `HirLowering.types_equal` (src/compiler/20.hir/hir_lowering/async.spl)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hir_types_equal_int_width_spec

Regression: `HirLowering.types_equal` (src/compiler/20.hir/hir_lowering/async.spl)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_types_equal_int_width_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression: `HirLowering.types_equal` (src/compiler/20.hir/hir_lowering/async.spl)
must distinguish `Int(bits, signed)` and `Float(bits)` payloads, not just their
outer discriminant. It is the equality oracle `check_poll_function_signature`
uses (async.spl:281) to decide whether a `poll` function's declared
`Poll<T>` inner type actually matches the async function's declared
`Future<T>` inner type -- so if `types_equal` says `i32 == i64`, a poll
function can declare the wrong-width state payload and this check silently
accepts it instead of reporting `future_type_param_mismatch`.

## Scenarios

### HirLowering.types_equal distinguishes numeric widths

#### treats i64 as equal to itself

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats i64 as equal to itself
   - Expected: lowering.types_equal(int_type(64, true), int_type(64, true)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats i64 as equal to itself")
var lowering = HirLowering.with_filename("types_equal_probe")
expect(lowering.types_equal(int_type(64, true), int_type(64, true))).to_equal(true)
```

</details>

#### does NOT treat i32 and i64 as equal (different bit widths)

- does NOT treat i32 and i64 as equal (different bit widths)
   - Expected: lowering.types_equal(int_type(32, true), int_type(64, true)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT treat i32 and i64 as equal (different bit widths)")
var lowering = HirLowering.with_filename("types_equal_probe")
expect(lowering.types_equal(int_type(32, true), int_type(64, true))).to_equal(false)
```

</details>

#### does NOT treat i64 and u64 as equal (different signedness)

- does NOT treat i64 and u64 as equal (different signedness)
   - Expected: lowering.types_equal(int_type(64, true), int_type(64, false)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT treat i64 and u64 as equal (different signedness)")
var lowering = HirLowering.with_filename("types_equal_probe")
expect(lowering.types_equal(int_type(64, true), int_type(64, false))).to_equal(false)
```

</details>

#### does NOT treat f32 and f64 as equal (different bit widths)

- does NOT treat f32 and f64 as equal (different bit widths)
   - Expected: lowering.types_equal(float_type(32), float_type(64)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT treat f32 and f64 as equal (different bit widths)")
var lowering = HirLowering.with_filename("types_equal_probe")
expect(lowering.types_equal(float_type(32), float_type(64))).to_equal(false)
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ecd680b8a2db720033945cafbcc416159e77cda43ddc629a554d9292d2b252b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecd680b8a2db720033945cafbcc416159e77cda43ddc629a554d9292d2b252b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecd680b8a2db720033945cafbcc416159e77cda43ddc629a554d9292d2b252b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_types_equal_int_width_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_types_equal_int_width_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_types_equal_int_width_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_types_equal_int_width_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_types_equal_int_width_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats i64 as equal to itself' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_types_equal_int_width_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT treat i32 and i64 as equal (different bit widths)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_types_equal_int_width_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT treat i64 and u64 as equal (different signedness)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
