# Implicit-self field assignment must never silently no-op

> Regression spec for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Implicit-self field assignment must never silently no-op

Regression spec for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/implicit_self_field_assign_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression spec for
`doc/08_tracking/bug/interp_implicit_self_field_assignment_silent_noop_2026-07-17.md`.

Inside a `me` method, a bare `field = value` (without `self.`) used to fall
through the AST interpreter's *implicit declaration* path: it minted a fresh
local that shadowed the receiver's field, so `self.field` was left untouched
and the program carried on with a silently wrong value.

Every other lane already rejected that shape --- HIR lowering (`unresolved
name`), MIR lowering (`assignment target has no local binding`), native LLVM
codegen (`llvm global store referenced undeclared symbol`), and the
pure-Simple interpreter (`undefined variable`). The seed's AST interpreter
was the sole outlier, and it was *asymmetric* with itself: a bare field READ
already raised E1001 `variable ... not found`, only the WRITE was silent.

`.claude/memory/ref_coding.md` documents the convention as `self.field` in
the body --- "implicit self" means omitting `self` from the *parameter list*,
not from field access --- so the fix makes the write path loud rather than
inventing implicit field resolution.

This spec drives the seed as a subprocess because the corrected behaviour is
a hard error that aborts the program under test; it cannot be observed from
inside the same interpreter run.

## Scenarios

### implicit-self field assignment in a me method

#### rejects a bare field assignment instead of silently discarding it

- rejects a bare field assignment instead of silently discarding it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a bare field assignment instead of silently discarding it")
val path = write_case("implicit", IMPLICIT_SRC)
val (_output, code) = run_case(path)
# The core regression: the old build exited 0 having printed
# IMPLICIT_RESULT=false, i.e. the mutation was silently dropped.
assert_not_equal(code, 0)
```

</details>

#### never reports the silently-unmutated field value

- never reports the silently-unmutated field value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never reports the silently-unmutated field value")
val path = write_case("implicit_value", IMPLICIT_SRC)
assert_equal(output_match_count(path, "IMPLICIT_RESULT=false"), "0")
```

</details>

#### names the shadowed field and points at the self. form

- names the shadowed field and points at the self. form


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the shadowed field and points at the self. form")
val path = write_case("implicit_msg", IMPLICIT_SRC)
val (output, _code) = run_case(path)
assert_contains(output, "is a field of")
assert_contains(output, "self.flag")
```

</details>

#### still applies an explicit self.field assignment

- still applies an explicit self.field assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still applies an explicit self.field assignment")
val path = write_case("explicit", EXPLICIT_SRC)
val (output, code) = run_case(path)
assert_contains(output, "EXPLICIT_RESULT=true")
assert_equal(code, 0)
```

</details>

#### leaves a bare non-field local assignment working

- leaves a bare non-field local assignment working


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a bare non-field local assignment working")
val path = write_case("plain_local", PLAIN_LOCAL_SRC)
val (output, code) = run_case(path)
assert_contains(output, "PLAIN_RESULT=42")
assert_equal(code, 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `edd57ecbf3047809e7ccf6f3d1e83a030d3239ab26efe504506471afeb613bb4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edd57ecbf3047809e7ccf6f3d1e83a030d3239ab26efe504506471afeb613bb4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edd57ecbf3047809e7ccf6f3d1e83a030d3239ab26efe504506471afeb613bb4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/implicit_self_field_assign_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/implicit_self_field_assign_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/implicit_self_field_assign_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/implicit_self_field_assign_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/implicit_self_field_assign_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a bare field assignment instead of silently discarding it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/implicit_self_field_assign_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never reports the silently-unmutated field value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/implicit_self_field_assign_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the shadowed field and points at the self. form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
