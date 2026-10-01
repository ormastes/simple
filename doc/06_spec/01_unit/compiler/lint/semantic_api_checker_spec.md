# semantic_api_checker_spec

> Purpose: Prove that semantic_api recursive checker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# semantic_api_checker_spec

Purpose: Prove that semantic_api recursive checker.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/semantic_api_checker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that semantic_api recursive checker.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### semantic_api recursive checker

#### fn signatures (MC-API-001)

#### flags a bare i64 parameter

- flags a bare i64 parameter
- Verify: flags a bare i64 parameter
   - Expected: vs.len() equals `1`
   - Expected: vs[0].code equals `MC-API-001`
   - Expected: vs[0].leaf equals `i64`
   - Expected: vs[0].member equals `param 'port'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a bare i64 parameter")
step("Verify: flags a bare i64 parameter")
# @req: REQ-COMPILER-LINT-001
val vs = check_fn_signature("set_port", ["port: i64"], "", false)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-001")
expect(vs[0].leaf).to_equal("i64")
expect(vs[0].member).to_equal("param 'port'")
```

</details>

#### flags a bare bool return

- flags a bare bool return
- Verify: flags a bare bool return
   - Expected: vs.len() equals `1`
   - Expected: vs[0].code equals `MC-API-001`
   - Expected: vs[0].member equals `return`
   - Expected: vs[0].leaf equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a bare bool return")
step("Verify: flags a bare bool return")
val vs = check_fn_signature("is_ready", ["cfg: Config"], "bool", false)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-001")
expect(vs[0].member).to_equal("return")
expect(vs[0].leaf).to_equal("bool")
```

</details>

#### flags Option<bool> — wrapping in Option does not launder a primitive

- flags Option<bool> — wrapping in Option does not launder a primitive
- Verify: flags Option<bool> — wrapping in Option does not launder a primitive
   - Expected: vs.len() equals `1`
   - Expected: vs[0].leaf equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags Option<bool> — wrapping in Option does not launder a primitive")
step("Verify: flags Option<bool> — wrapping in Option does not launder a primitive")
val vs = check_fn_signature("try_flag", [], "Option<bool>", false)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].leaf).to_equal("bool")
```

</details>

#### flags nested Dict<text, Option<i32>>

- flags nested Dict<text, Option<i32>>
- Verify: flags nested Dict<text, Option<i32>>
   - Expected: vs.len() equals `1`
   - Expected: vs[0].leaf equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags nested Dict<text, Option<i32>>")
step("Verify: flags nested Dict<text, Option<i32>>")
val vs = check_fn_signature("lookup", ["m: Dict<text, Option<i32>>"], "", false)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].leaf).to_equal("i32")
```

</details>

#### has NO pure-math exemption (abs-style fn still flagged)

- has NO pure-math exemption (abs-style fn still flagged)
- Verify: has NO pure-math exemption (abs-style fn still flagged)
   - Expected: vs.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has NO pure-math exemption (abs-style fn still flagged)")
step("Verify: has NO pure-math exemption (abs-style fn still flagged)")
val vs = check_fn_signature("abs", ["x: f64"], "f64", false)
expect(vs.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### skips the receiver but not other params

- skips the receiver but not other params
- Verify: skips the receiver but not other params
   - Expected: vs.len() equals `1`
   - Expected: vs[0].leaf equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips the receiver but not other params")
step("Verify: skips the receiver but not other params")
val vs = check_fn_signature("scale", ["self", "factor: f32"], "", false)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].leaf).to_equal("f32")
```

</details>

#### recurses arrays, tuples and unions

- recurses arrays, tuples and unions
- Verify: recurses arrays, tuples and unions
   - Expected: semantic_api_primitive_leaves("[Option<u16>]").len() equals `1`
   - Expected: semantic_api_primitive_leaves("(Name, i8)").len() equals `1`
   - Expected: semantic_api_primitive_leaves("Name | u64").len() equals `1`
   - Expected: semantic_api_primitive_leaves("Result<Ok, [(text, Option<i16>)]>").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recurses arrays, tuples and unions")
step("Verify: recurses arrays, tuples and unions")
expect(semantic_api_primitive_leaves("[Option<u16>]").len()).to_equal(1)
expect(semantic_api_primitive_leaves("(Name, i8)").len()).to_equal(1)
expect(semantic_api_primitive_leaves("Name | u64").len()).to_equal(1)
expect(semantic_api_primitive_leaves("Result<Ok, [(text, Option<i16>)]>").len()).to_equal(1)
```

</details>

#### leaves domain-typed signatures clean

- leaves domain-typed signatures clean
- Verify: leaves domain-typed signatures clean
   - Expected: vs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves domain-typed signatures clean")
step("Verify: leaves domain-typed signatures clean")
val vs = check_fn_signature("send", ["msg: Message", "to: Address"], "DeliveryReceipt", false)
expect(vs.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### newunit awareness

#### treats a registered newunit as clean

- treats a registered newunit as clean
- Verify: treats a registered newunit as clean
   - Expected: semantic_api_is_newunit("RetryCount") is true
   - Expected: vs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a registered newunit as clean")
step("Verify: treats a registered newunit as clean")
newunit_register("RetryCount", "retries", TYPE_I64)
expect(semantic_api_is_newunit("RetryCount")).to_equal(true)
val vs = check_fn_signature("with_retries", ["n: RetryCount"], "RetryCount", false)
expect(vs.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### treats Option<newunit> as clean

- treats Option<newunit> as clean
- Verify: treats Option<newunit> as clean
   - Expected: semantic_api_primitive_leaves("Option<RetryCount>").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats Option<newunit> as clean")
step("Verify: treats Option<newunit> as clean")
newunit_register("RetryCount", "retries", TYPE_I64)
expect(semantic_api_primitive_leaves("Option<RetryCount>").len()).to_equal(0)
```

</details>

#### struct/class fields (MC-API-002)

#### flags a bare u8 struct field

- flags a bare u8 struct field
- Verify: flags a bare u8 struct field
   - Expected: vs.len() equals `1`
   - Expected: vs[0].code equals `MC-API-002`
   - Expected: vs[0].leaf equals `u8`
   - Expected: vs[0].member equals `field 'flags'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a bare u8 struct field")
step("Verify: flags a bare u8 struct field")
val vs = check_field_texts("Packet", ["flags: u8", "payload: Bytes"])
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-002")
expect(vs[0].leaf).to_equal("u8")
expect(vs[0].member).to_equal("field 'flags'")
```

</details>

#### extern fns (MC-API-003, informational — not skipped)

#### reports extern signatures under the distinct code

- reports extern signatures under the distinct code
- Verify: reports extern signatures under the distinct code
   - Expected: vs.len() equals `3`
   - Expected: vs[0].code equals `MC-API-003`
   - Expected: vs[2].code equals `MC-API-003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports extern signatures under the distinct code")
step("Verify: reports extern signatures under the distinct code")
val vs = check_fn_signature("rt_read", ["fd: i64", "len: i64"], "i64", true)
expect(vs.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-003")
expect(vs[2].code).to_equal("MC-API-003")
```

</details>

#### parses an 'extern fn' declaration line

- parses an 'extern fn' declaration line
- Verify: parses an 'extern fn' declaration line
   - Expected: vs.len() equals `2`
   - Expected: vs[0].code equals `MC-API-003`
   - Expected: vs[0].leaf equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses an 'extern fn' declaration line")
step("Verify: parses an 'extern fn' declaration line")
val vs = check_extern_signature_text("extern fn rt_env_get_i64(key: text, default_value: i64) -> i64")
expect(vs.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-003")
expect(vs[0].leaf).to_equal("i64")
```

</details>

#### alias resolution hook

#### is fail-open until alias metadata exists (documented gap)

- is fail-open until alias metadata exists (documented gap)
- Verify: is fail-open until alias metadata exists (documented gap)
   - Expected: semantic_api_resolve_alias("Fd") equals ``
   - Expected: semantic_api_primitive_leaves("Fd").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is fail-open until alias metadata exists (documented gap)")
step("Verify: is fail-open until alias metadata exists (documented gap)")
# No alias registry at the 35.semantics layer: hook returns ""
# and an alias-of-primitive is NOT flagged (fail-open, loud).
expect(semantic_api_resolve_alias("Fd")).to_equal("")
expect(semantic_api_primitive_leaves("Fd").len()).to_equal(0)
```

</details>

#### module-items entry point

#### walks Function and Struct nodes and emits distinct codes

- walks Function and Struct nodes and emits distinct codes
- Verify: walks Function and Struct nodes and emits distinct codes
   - Expected: vs.len() equals `3`
   - Expected: vs[0].code equals `MC-API-001`
   - Expected: vs[0].leaf equals `i64`
   - Expected: vs[1].code equals `MC-API-001`
   - Expected: vs[1].member equals `return`
   - Expected: vs[2].code equals `MC-API-002`
   - Expected: vs[2].leaf equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("walks Function and Struct nodes and emits distinct codes")
step("Verify: walks Function and Struct nodes and emits distinct codes")
val fd = FunctionDef(
    name: "resize",
    generic_params: [],
    params: ["self", "w: i64", "h: Height"],
    return_type: "bool",
    body: [],
    is_generic_template: false,
    specialization_of: "",
    type_bindings: {}
)
val sd = StructDef(
    name: "Pixel",
    generic_params: [],
    fields: ["r: u8", "color: Color"],
    is_generic_template: false,
    specialization_of: "",
    type_bindings: {}
)
val items = [Node.Function(fd), Node.Struct(sd)]
val vs = check_module_items(items)
expect(vs.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-001")
expect(vs[0].leaf).to_equal("i64")
expect(vs[1].code).to_equal("MC-API-001")
expect(vs[1].member).to_equal("return")
expect(vs[2].code).to_equal("MC-API-002")
expect(vs[2].leaf).to_equal("u8")
```

</details>

#### emits MC-API-003 for extern lines carried as Other nodes

- emits MC-API-003 for extern lines carried as Other nodes
- Verify: emits MC-API-003 for extern lines carried as Other nodes
   - Expected: vs.len() equals `1`
   - Expected: vs[0].code equals `MC-API-003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits MC-API-003 for extern lines carried as Other nodes")
step("Verify: emits MC-API-003 for extern lines carried as Other nodes")
val items = [Node.Other("extern fn rt_now() -> i64")]
val vs = check_module_items(items)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].code).to_equal("MC-API-003")
```

</details>

#### enum payloads (lane A4E, 2026-07-29 — confirmed structural blocker)

#### emits nothing for an enum, even one whose variant text encodes a primitive payload

- emits nothing for an enum, even one whose variant text encodes a primitive payload
- Verify: emits nothing for an enum, even one whose variant text encodes a primitive payload
   - Expected: vs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits nothing for an enum, even one whose variant text encodes a primitive payload")
step("Verify: emits nothing for an enum, even one whose variant text encodes a primitive payload")
# Ground truth (doc/08_tracking/bug/enum_variant_payload_types_discarded_at_parse_2026-07-29.md):
# the core parser discards variant payload types at the token
# level (parser_decls_types.spl:140, enum_module_body.spl:150/155)
# and the one production flat-AST bridge that builds real
# Enum/Variant nodes from parsed source hardcodes an empty
# payload for every variant (_FlatAstBridge/module_assembly.spl:390).
# There is no AST structure to walk, so check_module_items must
# stay silent on Enum nodes -- this pins that honest behavior
# rather than leaving it an unverified assumption.
val ed = EnumDef(
    name: "BadEnum",
    generic_params: [],
    variants: ["Bad(payload: i64)", "Clean"],
    is_generic_template: false,
    specialization_of: "",
    type_bindings: {}
)
val vs = check_module_items([Node.Enum(ed)])
expect(vs.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-LINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d402831acbb2179ce382750f64a7d8823ff3d052275db0a4687f193fac1f83f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d402831acbb2179ce382750f64a7d8823ff3d052275db0a4687f193fac1f83f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d402831acbb2179ce382750f64a7d8823ff3d052275db0a4687f193fac1f83f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/semantic_api_checker_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/semantic_api_checker_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/semantic_api_checker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/semantic_api_checker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/semantic_api_checker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/semantic_api_checker_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a bare i64 parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/semantic_api_checker_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a bare bool return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/semantic_api_checker_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags Option<bool> — wrapping in Option does not launder a primitive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
