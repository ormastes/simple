# Union Narrowing Unit Spec (Wave 2D lane S4 follow-up)

> Proves a structural union can be NARROWED in source, which lane S4 left

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Union Narrowing Unit Spec (Wave 2D lane S4 follow-up)

Proves a structural union can be NARROWED in source, which lane S4 left

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/union_narrowing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves a structural union can be NARROWED in source, which lane S4 left
impossible: `case i64 v:` was a parse error and `if x is i64:` lowered `i64`
as a VALUE ("unresolved identifier 'i64'").

Bug: doc/08_tracking/bug/union_narrowing_has_no_grammar_or_runtime_2026-08-21.md
Design: doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md
        §10.3 ("exhaustive narrowing"), §10.1, §8.4.

The grammar is a type-pattern arm in the position an enum-variant arm already
occupies:

    match x:                      # x: i64 | f64 | bool | text
        case i64 v: ...
        case text s: ...
        case nil: ...             # unchanged nil pattern; `T?` == `T | nil`

The load-bearing claim is not that the arms parse but that they lower to
variants of the SYNTHESIZED `__Union_...` enum, so exhaustiveness, the closed
contract and E-CLOSED-001 govern them through the machinery that already
exists. Each case below fails if that rewrite regresses to a wildcard, a
binding, or an if-chain (all three of which would silently accept a match that
misses a member).

## Scenarios

### type-pattern name mapping

#### maps a written type name to its union variant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps a written type name to its union variant
   - Expected: union_narrow_variant_name("i64") equals `I64`
   - Expected: union_narrow_variant_name("f64") equals `F64`
   - Expected: union_narrow_variant_name("bool") equals `Bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps a written type name to its union variant")
expect(union_narrow_variant_name("i64")).to_equal("I64")
expect(union_narrow_variant_name("f64")).to_equal("F64")
expect(union_narrow_variant_name("bool")).to_equal("Bool")
```

</details>

#### keys `str` and `text` to the SAME member, since both spell one type

- keys `str` and `text` to the SAME member, since both spell one type
   - Expected: union_narrow_member_key_for_type_name("str") equals `text`
   - Expected: union_narrow_member_key_for_type_name("text") equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys `str` and `text` to the SAME member, since both spell one type")
expect(union_narrow_member_key_for_type_name("str")).to_equal("text")
expect(union_narrow_member_key_for_type_name("text")).to_equal("text")
```

</details>

#### names E-NARROW-001 explicitly in its message

- names E-NARROW-001 explicitly in its message
   - Expected: union_narrow_error_text("i64", "v") contains `E-NARROW-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names E-NARROW-001 explicitly in its message")
expect(union_narrow_error_text("i64", "v").contains("E-NARROW-001")).to_equal(true)
```

</details>

### grammar

#### accepts `case i64 v:` where a variant arm goes -- and binds the value

- accepts `case i64 v:` where a variant arm goes -- and binds the value
   - Expected: site.coverage.has_wildcard is false
   - Expected: sites equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts `case i64 v:` where a variant arm goes -- and binds the value")
# A parse failure would surface as zero match sites below, and a
# pattern misread as a Binding or a Wildcard would surface as
# has_wildcard -- so this case pins the grammar through its effect,
# not through the parse tree shape.
val src = "fn f(x: i64 | text) -> i64:\n    match x:\n        case i64 v: v\n        case text s: 0\n"
val hm = lower_source(src, "g1")
var sites = 0
for site in hir_enum_match_sites(hm):
    sites = sites + 1
    expect(site.coverage.has_wildcard).to_equal(false)
expect(sites).to_equal(1)
```

</details>

#### does NOT steal `x is y` between two VALUES

- does NOT steal `x is y` between two VALUES
   - Expected: binaries equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT steal `x is y` between two VALUES")
# The `is`-narrowing rule fires only when the right operand NAMES a
# type. A lowercase identifier is a value, and must keep the ordinary
# binary-comparison lowering.
val src = "fn f(a: i64, b: i64) -> bool:\n    a is b\n"
val hm = lower_source(src, "g2")
var binaries = 0
for f in hm.functions.values():
    if f.body.has:
        match f.body.value.kind:
            case HirExprKind.Binary(op, l, r): binaries = binaries + 1
            case other_expr_kind: binaries = binaries
expect(binaries).to_equal(1)
```

</details>

### lowering to the synthesized union enum

#### rewrites every narrowing arm into a `__Union_...` variant arm

- rewrites every narrowing arm into a `__Union_...` variant arm
   - Expected: site.coverage.enum_name equals `__Union_i64_text`
   - Expected: enum_arms equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites every narrowing arm into a `__Union_...` variant arm")
val src = "fn f(x: i64 | text) -> i64:\n    match x:\n        case i64 v: v\n        case text s: 0\n"
val hm = lower_source(src, "n1")
var enum_arms = 0
for site in hir_enum_match_sites(hm):
    expect(site.coverage.enum_name).to_equal("__Union_i64_text")
    enum_arms = enum_arms + site.coverage.covered_variant_ids.len()
expect(enum_arms).to_equal(2)
```

</details>

#### reports a match that misses a member as NON-exhaustive

- reports a match that misses a member as NON-exhaustive
   - Expected: site.coverage.all_variant_ids.len() equals `3`
   - Expected: site.coverage.covered_variant_ids.len() equals `2`
   - Expected: site.coverage.has_wildcard is false
   - Expected: sites equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a match that misses a member as NON-exhaustive")
val src = "fn f(x: i64 | text | bool) -> i64:\n    match x:\n        case i64 v: v\n        case text s: 0\n"
val hm = lower_source(src, "n2")
var sites = 0
for site in hir_enum_match_sites(hm):
    sites = sites + 1
    expect(site.coverage.all_variant_ids.len()).to_equal(3)
    expect(site.coverage.covered_variant_ids.len()).to_equal(2)
    expect(site.coverage.has_wildcard).to_equal(false)
expect(sites).to_equal(1)
```

</details>

#### counts `case nil:` as the union's nil member, not as a wildcard

- counts `case nil:` as the union's nil member, not as a wildcard
   - Expected: site.coverage.enum_name equals `__Union_i64_nil_text`
   - Expected: site.coverage.covered_variant_ids.len() equals `3`
   - Expected: site.coverage.has_wildcard is false
   - Expected: sites equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts `case nil:` as the union's nil member, not as a wildcard")
val src = "fn f(x: i64? | text) -> i64:\n    match x:\n        case i64 v: v\n        case text s: 0\n        case nil: 9\n"
val hm = lower_source(src, "n3")
var sites = 0
for site in hir_enum_match_sites(hm):
    sites = sites + 1
    expect(site.coverage.enum_name).to_equal("__Union_i64_nil_text")
    expect(site.coverage.covered_variant_ids.len()).to_equal(3)
    expect(site.coverage.has_wildcard).to_equal(false)
expect(sites).to_equal(1)
```

</details>

### non-union scrutinee

#### reports E-NARROW-001 rather than silently accepting the arm

- reports E-NARROW-001 rather than silently accepting the arm
   - Expected: narrow_errors > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports E-NARROW-001 rather than silently accepting the arm")
# A type pattern narrows a UNION member. Over a plain `i64` it means
# nothing, and the failure mode that must never return is silence:
# before this change the arm did not parse at all, and the wrong fix
# would be to let it through as a catch-all.
val src = "fn f(x: i64) -> i64:\n    match x:\n        case i64 v: v\n        case _: 0\n"
val path = "spec://nn1.spl"
val parsed = parse_full_frontend(src, path, "nn1", Logger(level: 0))
var hl = HirLowering.with_filename(path)
val lowered = hl.lower_module(parsed)
var narrow_errors = 0
for e in hl.errors:
    if e.message.contains("E-NARROW-001"):
        narrow_errors = narrow_errors + 1
# At least one: the arm is reported where the union rewrite declines
# it, and again if it survives to match lowering. Both are loud; the
# claim is that NEITHER is silent.
expect(narrow_errors > 0).to_equal(true)
```

</details>

### `x is T`

#### lowers a type-named right operand to a TypeTest expression, not a value load

- lowers a type-named right operand to a TypeTest expression, not a value load
   - Expected: type_name equals `i64`
   - Expected: type_tests equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers a type-named right operand to a TypeTest expression, not a value load")
val src = "fn f(x: i64 | text) -> bool:\n    x is i64\n"
val hm = lower_source(src, "is1")
var type_tests = 0
for f in hm.functions.values():
    if f.body.has:
        match f.body.value.kind:
            case HirExprKind.TypeTest(value, type_name):
                expect(type_name).to_equal("i64")
                type_tests = type_tests + 1
            case other_expr_kind: type_tests = type_tests
expect(type_tests).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `1ec510c8b0fa3255fe0bc8cbc685720adbff9f26226710e7c2bdd82491fe2499`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ec510c8b0fa3255fe0bc8cbc685720adbff9f26226710e7c2bdd82491fe2499`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ec510c8b0fa3255fe0bc8cbc685720adbff9f26226710e7c2bdd82491fe2499`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/semantics/union_narrowing_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/union_narrowing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/union_narrowing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/union_narrowing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/union_narrowing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/semantics/union_narrowing_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps a written type name to its union variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/union_narrowing_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keys `str` and `text` to the SAME member, since both spell one type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/union_narrowing_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names E-NARROW-001 explicitly in its message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
