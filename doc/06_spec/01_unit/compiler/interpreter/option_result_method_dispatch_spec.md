# Option Result Method Dispatch Specification

> Tests covering interpreter Option/Result method dispatch, interpreter array reduce dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Result Method Dispatch Specification

## Scenarios

### interpreter Option/Result method dispatch

#### unwrap yields the payload and unwrap_or falls back

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- unwrap yields the payload and unwrap_or falls back
   - Expected: some_v.unwrap_or(7) equals `42`
   - Expected: none_v.unwrap_or(7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwrap yields the payload and unwrap_or falls back")
# NOTE ON ENGINE: this block executes on whichever engine runs the
# suite -- today that is the Rust seed child, NOT the pure-Simple
# interpreter. It pins the cross-lane contract the pure-Simple arms
# were written to match. The pure-Simple interpreter's own conformance
# was measured separately by driving core_interpret_expr with the seed
# as HOST over working-copy source; the structural blocks below are the
# regression pin for that measurement.
val some_v: i64? = 42
expect(some_v.unwrap_or(7)).to_equal(42)
val none_v: i64? = nil
expect(none_v.unwrap_or(7)).to_equal(7)
```

</details>

#### the LIVE dispatch routes Option/Result methods before the per-kind split

- the LIVE dispatch routes Option/Result methods before the per-kind split


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the LIVE dispatch routes Option/Result methods before the per-kind split")
# An Option has no value kind of its own in this interpreter -- there is
# no VAL_ENUM. Under the FLAT encoding a Some(text) IS a plain text, so
# if the Option check ran after the per-kind dispatch it would be
# swallowed by eval_text_method and rejected there. The check must
# therefore sit BEFORE `if kind == VAL_ARRAY:`.
val source = live_dispatch_source()
expect(source).to_contain("fn eval_option_result_method")
expect(source).to_contain("fn is_option_result_method")

val gate_pos = source.index_of("if is_option_result_method(method_name):")
expect(gate_pos).to_be_greater_than(-1)
val array_pos = source.index_of("if kind == VAL_ARRAY:")
expect(array_pos).to_be_greater_than(gate_pos)
```

</details>

#### discriminates on __tag, never on the struct name

- discriminates on __tag, never on the struct name


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("discriminates on __tag, never on the struct name")
# The two producers of a boxed Option DISAGREE on the struct name:
# eval_enum_variant_call names it "Option::Some" / "Result::Ok"
# (Type::Variant) while eval_text_method's parse_int arm names it plain
# "Option". Only the `__tag` field is a reliable discriminator, which is
# what val_is_boxed_enum keys on. Measured, not assumed:
#   "1234".parse_int() => struct name='Option' __tag='Some'
val source = live_dispatch_source()
val tag_fn = arm_body(source, "fn option_result_tag", "fn option_result_payload")
expect(tag_fn).to_contain("val_is_boxed_enum")
expect(tag_fn).to_contain("__tag")
expect(tag_fn).to_not_contain("val_get_struct_name(receiver) ==")
```

</details>

#### unwrap on None/Err FAILS LOUDLY and never returns a plausible value

- unwrap on None/Err FAILS LOUDLY and never returns a plausible value


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwrap on None/Err FAILS LOUDLY and never returns a plausible value")
# This is the whole point of the arm. Before it existed the live path
# errored loudly BY ACCIDENT (no arm matched). That property is now
# deliberate: every non-present branch must reach eval_set_error and
# return -1. A silent 0 / nil / receiver here is the exact shape of the
# P0 in doc/08_tracking/bug/deep_recheck_2026-07-05.md.
# Anchor inside eval_option_result_method: the literal
# `if method_name == "unwrap":` also appears earlier, in the
# is_option_result_method predicate list.
val source = arm_body(live_dispatch_source(),
    "fn eval_option_result_method", "# ===== Array Methods =====")
val unwrap_body = arm_body(source,
    "if method_name == \"unwrap\":",
    "if method_name == \"unwrap_err\":")
expect(unwrap_body).to_contain("eval_set_error(\"called unwrap on None\")")
expect(unwrap_body).to_contain("called unwrap on Err")
expect(unwrap_body).to_not_contain("return val_make_int(0)")
expect(unwrap_body).to_not_contain("return val_make_nil()")

val unwrap_err_body = arm_body(source,
    "if method_name == \"unwrap_err\":",
    "if method_name == \"unwrap_or\":")
expect(unwrap_err_body).to_contain("eval_set_error")
expect(unwrap_err_body).to_not_contain("return val_make_nil()")
```

</details>

#### covers the full predicate set

- covers the full predicate set


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("covers the full predicate set")
val source = live_dispatch_source()
val gate = arm_body(source, "fn is_option_result_method", "fn option_result_tag")
expect(gate).to_contain("\"unwrap\"")
expect(gate).to_contain("\"unwrap_or\"")
expect(gate).to_contain("\"unwrap_err\"")
expect(gate).to_contain("\"is_some\"")
expect(gate).to_contain("\"is_none\"")
expect(gate).to_contain("\"is_ok\"")
expect(gate).to_contain("\"is_err\"")
```

</details>

#### leaves a plain user struct on the user-method path

- leaves a plain user struct on the user-method path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves a plain user struct on the user-method path")
# A non-enum VAL_STRUCT must NOT be diverted, so a user-defined
# Type__unwrap still wins on the struct-method path.
val source = live_dispatch_source()
expect(source).to_contain("val_is_boxed_enum(receiver) == false")
```

</details>

### interpreter array reduce dispatch

#### the LIVE array dispatch has a reduce arm using the map/filter closure convention

- the LIVE array dispatch has a reduce arm using the map/filter closure convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the LIVE array dispatch has a reduce arm using the map/filter closure convention")
# reduce(initial, fn(acc, item)). NOTE: unlike the Option arms above,
# this one is NOT behaviourally verified in the pure-Simple lane -- a
# closure cannot be driven through core_interpret_expr at all. The
# pre-existing `map` arm crashes there identically
# ("array index out of bounds: index is 0 but length is 0"), so the
# harness, not the arm, is the blocker. Verified by structural parity
# with map/filter/flat_map only.
val source = live_dispatch_source()
val body = arm_body(source,
    "if method_name == \"reduce\" or method_name == \"fold\":",
    "if method_name == \"any\":")
expect(body).to_contain("val_is_function")
expect(body).to_contain("eval_method_with_args")
expect(body).to_contain("[acc, item]")
# Misuse must be loud, not a silent identity return.
expect(body).to_contain("eval_set_error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter Option/Result method dispatch, interpreter array reduce dispatch.
- interpreter Option/Result method dispatch
- interpreter array reduce dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `76d41adc69739eb006554219308ef83cbfedc1284c1dd1737f60584b9de60bcf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76d41adc69739eb006554219308ef83cbfedc1284c1dd1737f60584b9de60bcf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76d41adc69739eb006554219308ef83cbfedc1284c1dd1737f60584b9de60bcf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/option_result_method_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/option_result_method_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/option_result_method_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwrap yields the payload and unwrap_or falls back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the LIVE dispatch routes Option/Result methods before the per-kind split' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discriminates on __tag, never on the struct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
