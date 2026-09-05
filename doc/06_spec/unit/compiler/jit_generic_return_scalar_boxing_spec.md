# Generic Scalar Return / Generic Struct Field Boxing (JIT lane)

> A generic type parameter resolves to `TypeId::ANY`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Scalar Return / Generic Struct Field Boxing (JIT lane)

A generic type parameter resolves to `TypeId::ANY`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/jit_generic_return_scalar_boxing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A generic type parameter resolves to `TypeId::ANY`
(hir/lower/type_resolver.rs), so a generic function's RETURN slot is a
tagged slot and `HirStmt::Return` boxes into it. Nothing unboxed on the way
back: a scalar `T` picked up one `<< 3` per generic hop, so
`ai = ident(ai) + 1` twice yielded 72 instead of 2. A generic struct's field
is the same slot in a different coat -- the raw scalar was stored into an
`ANY` field and read back as a tagged word, printing `<value:0x5>`.

Regression cover for
doc/08_tracking/bug/generic_struct_field_untagged_payload_seed_2026-08-21.md.

**This spec must shell out.** `bin/simple test` overwrites
SIMPLE_EXECUTION_MODE to "interpret" before every child spec
(src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl), and the
interpreter was always CORRECT here -- an in-process assertion would be
green on a broken compiler. So it runs the fixture through `simple run`
under both engines, exactly like
scripts/check/check_jit_interpreter_differential.spl, and requires the JIT
lane to agree with the interpreter AND with pinned ground truth.
Set SIMPLE_BIN to target a specific binary; default `bin/simple`.

## Scenarios

### generic scalar return and generic struct field under the JIT

#### returns an i64 through a generic fn without a per-hop tag shift

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns an i64 through a generic fn without a per-hop tag shift


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an i64 through a generic fn without a per-hop tag shift")
expect(jit_output()).to_contain("i64chain=2")
```

</details>

#### returns an f64 through a generic fn as a real double

- returns an f64 through a generic fn as a real double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an f64 through a generic fn as a real double")
expect(jit_output()).to_contain("f64chain=1.5")
```

</details>

#### returns bool and text through a generic fn unchanged

- returns bool and text through a generic fn unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns bool and text through a generic fn unchanged")
val out = jit_output()
expect(out).to_contain("bool=true")
expect(out).to_contain("text=hi")
```

</details>

#### reads an i64 field of a generic struct as a number

- reads an i64 field of a generic struct as a number


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads an i64 field of a generic struct as a number")
expect(jit_output()).to_contain("ifield=5")
```

</details>

#### reads an f64 field of a generic struct as a double

- reads an f64 field of a generic struct as a double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads an f64 field of a generic struct as a double")
expect(jit_output()).to_contain("ffield=1.5")
```

</details>

#### agrees with the interpreter, which was always correct here

- agrees with the interpreter, which was always correct here


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with the interpreter, which was always correct here")
expect(interp_output()).to_contain("i64chain=2")
expect(interp_output()).to_contain("ifield=5")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7da0b1ffe626704c7d78b9afafe81e14ff70740b7528b32458819e04ab7d0c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7da0b1ffe626704c7d78b9afafe81e14ff70740b7528b32458819e04ab7d0c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7da0b1ffe626704c7d78b9afafe81e14ff70740b7528b32458819e04ab7d0c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/jit_generic_return_scalar_boxing_spec.spl
mirror: doc/06_spec/unit/compiler/jit_generic_return_scalar_boxing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/jit_generic_return_scalar_boxing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/jit_generic_return_scalar_boxing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/jit_generic_return_scalar_boxing_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an i64 through a generic fn without a per-hop tag shift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/jit_generic_return_scalar_boxing_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an f64 through a generic fn as a real double' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/jit_generic_return_scalar_boxing_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns bool and text through a generic fn unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
