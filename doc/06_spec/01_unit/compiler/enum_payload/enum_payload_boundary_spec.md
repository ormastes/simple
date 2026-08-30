# Enum Payload Metadata Boundary Spec (lane S1)

> Hardening plan `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Payload Metadata Boundary Spec (lane S1)

Hardening plan `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/enum_payload/enum_payload_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

```simple
Hardening plan `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`
§15 Phase 4 "preserve enum payload metadata end to end", §20.7 row S1.

Tracks the payload enum

    enum E:
        A(i64, text)
        B(name: text, n: i64)
        C

across the parser boundary, and asserts the four properties the plan names:

1. **arity**    -- a 2-field payload stays 2 fields, never collapses to 1 or 0;
2. **types**    -- each payload field's declared type survives POSITIONALLY,
                   in source order;
3. **names**    -- a NAMED payload field (`name: text`) keeps its field name;
4. **discriminant** -- an explicit `A = 1` reaches later stages as the GIVEN
                   value, not the variant's positional index.

Property 3 was the measured gap when this lane opened: the parser consumed the
payload field-name token and discarded it (`enum_module_body.spl`, the
`par_kind_get() == 6: parser_advance()` arm), `decl_enum_def` had no slot for
payload field names, and `_FlatAstBridge/module_assembly.spl` hardcoded
`VariantKind.Tuple(...)` for EVERY variant -- so a named payload was
indistinguishable from a positional one by the time anything downstream could
ask. `HirVariantKind.Struct([HirField])` and `VariantKind.Struct([ParserField])`
both already existed and were simply never constructed from source text.

HARNESS NOTE (matches enum_payload_capture_spec.spl / type_alias_capture_spec.spl
in this same area): the `parse_full_frontend` call is inlined in each `it` block
on purpose -- routing it through a shared module-level helper fn has previously
been shown to lose recorded parser/lowering state when read back afterward.

Dict landmine (.claude/rules/code-style.md): `enums` values are STRUCTS, so
presence/lookup goes through `contains_key(...)` + index read, never `.get()`.

```
## Scenarios

### enum payload metadata survives the parser boundary

#### preserves payload ARITY for a positional multi-field variant A(i64, text)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves payload ARITY for a positional multi-field variant A(i64, text)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves payload ARITY for a positional multi-field variant A(i64, text)")
val parsed = parse_full_frontend(FIXTURE, "testdata/s1_arity_a.spl", "s1_arity_a", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("E"))
val e = parsed.enums["E"]
val ai = find_variant_index(e.variants, "A")
assert_true(ai >= 0)
assert_equal(payload_type_names(e.variants[ai]).len(), 2)
```

</details>

#### preserves positional payload TYPES in source order for A(i64, text)

- preserves positional payload TYPES in source order for A(i64, text)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves positional payload TYPES in source order for A(i64, text)")
val parsed = parse_full_frontend(FIXTURE, "testdata/s1_types_a.spl", "s1_types_a", Logger(level: 0))
assert_false(parser_has_errors())
val e = parsed.enums["E"]
val ai = find_variant_index(e.variants, "A")
assert_true(ai >= 0)
val tys = payload_type_names(e.variants[ai])
assert_equal(tys.len(), 2)
assert_equal(tys[0], "i64")
assert_equal(tys[1], "text")
```

</details>

#### preserves payload ARITY and TYPES for a NAMED-payload variant B(name: text, n: i64)

- preserves payload ARITY and TYPES for a NAMED-payload variant B(name: text, n: i64)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves payload ARITY and TYPES for a NAMED-payload variant B(name: text, n: i64)")
val parsed = parse_full_frontend(FIXTURE, "testdata/s1_types_b.spl", "s1_types_b", Logger(level: 0))
assert_false(parser_has_errors())
val e = parsed.enums["E"]
val bi = find_variant_index(e.variants, "B")
assert_true(bi >= 0)
val tys = payload_type_names(e.variants[bi])
assert_equal(tys.len(), 2)
assert_equal(tys[0], "text")
assert_equal(tys[1], "i64")
```

</details>

#### preserves payload field NAMES for B(name: text, n: i64)

- preserves payload field NAMES for B(name: text, n: i64)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves payload field NAMES for B(name: text, n: i64)")
# The lane's headline property. Before the S1 fix this returned [] --
# every variant was lowered to VariantKind.Tuple, which has no names.
val parsed = parse_full_frontend(FIXTURE, "testdata/s1_names_b.spl", "s1_names_b", Logger(level: 0))
assert_false(parser_has_errors())
val e = parsed.enums["E"]
val bi = find_variant_index(e.variants, "B")
assert_true(bi >= 0)
val names = payload_field_names(e.variants[bi])
assert_equal(names.len(), 2)
assert_equal(names[0], "name")
assert_equal(names[1], "n")
```

</details>

#### keeps a positional payload NAMELESS -- A(i64, text) must not invent field names

- keeps a positional payload NAMELESS -- A(i64, text) must not invent field names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a positional payload NAMELESS -- A(i64, text) must not invent field names")
# The dual of the assertion above: recording names must not silently
# reclassify a positional payload as a named one.
val parsed = parse_full_frontend(FIXTURE, "testdata/s1_names_a.spl", "s1_names_a", Logger(level: 0))
assert_false(parser_has_errors())
val e = parsed.enums["E"]
val ai = find_variant_index(e.variants, "A")
assert_true(ai >= 0)
assert_equal(payload_field_names(e.variants[ai]).len(), 0)
```

</details>

#### leaves a payload-less variant C with zero payload fields

- leaves a payload-less variant C with zero payload fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a payload-less variant C with zero payload fields")
val parsed = parse_full_frontend(FIXTURE, "testdata/s1_unit_c.spl", "s1_unit_c", Logger(level: 0))
assert_false(parser_has_errors())
val e = parsed.enums["E"]
val ci = find_variant_index(e.variants, "C")
assert_true(ci >= 0)
assert_equal(payload_type_names(e.variants[ci]).len(), 0)
assert_equal(payload_field_names(e.variants[ci]).len(), 0)
```

</details>

#### records an explicit discriminant A = 1 as PRESENT on the variant

- records an explicit discriminant A = 1 as PRESENT on the variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records an explicit discriminant A = 1 as PRESENT on the variant")
val src = "enum D:\n" +
    "    A = 1\n" +
    "    B\n" +
    "\n" +
    "fn identity(n: i64) -> i64:\n" +
    "    n\n"
val parsed = parse_full_frontend(src, "testdata/s1_disc.spl", "s1_disc", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("D"))
val e = parsed.enums["D"]
val ai = find_variant_index(e.variants, "A")
assert_true(ai >= 0)
# `has_discriminant` is what MIR's lower_const_expr gate reads before
# it will honour the GIVEN value instead of the positional index
# (50.mir/_MirLowering/module_lowering.spl, `if variant.has_discriminant`).
assert_true(e.variants[ai].has_discriminant)
val bi = find_variant_index(e.variants, "B")
assert_true(bi >= 0)
assert_false(e.variants[bi].has_discriminant)
```

</details>

#### records an explicit discriminant on a variant that ALSO has a payload

- records an explicit discriminant on a variant that ALSO has a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records an explicit discriminant on a variant that ALSO has a payload")
# Payload capture and discriminant capture share the same parse loop
# iteration; neither may consume the other's tokens.
val src = "enum D:\n" +
    "    A(n: i64) = 7\n" +
    "    B\n" +
    "\n" +
    "fn identity(n: i64) -> i64:\n" +
    "    n\n"
val parsed = parse_full_frontend(src, "testdata/s1_disc_pay.spl", "s1_disc_pay", Logger(level: 0))
assert_false(parser_has_errors())
val e = parsed.enums["D"]
val ai = find_variant_index(e.variants, "A")
assert_true(ai >= 0)
assert_true(e.variants[ai].has_discriminant)
assert_equal(payload_type_names(e.variants[ai]).len(), 1)
assert_equal(payload_field_names(e.variants[ai])[0], "n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `deb80d06a7d2f5b2f669429d03f766ba3881cf3a2dc730ff96e03b9b4c490661`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `deb80d06a7d2f5b2f669429d03f766ba3881cf3a2dc730ff96e03b9b4c490661`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `deb80d06a7d2f5b2f669429d03f766ba3881cf3a2dc730ff96e03b9b4c490661`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/enum_payload/enum_payload_boundary_spec.spl
mirror: doc/06_spec/01_unit/compiler/enum_payload/enum_payload_boundary_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/enum_payload/enum_payload_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/enum_payload/enum_payload_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/enum_payload/enum_payload_boundary_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves payload ARITY for a positional multi-field variant A(i64, text)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/enum_payload/enum_payload_boundary_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves positional payload TYPES in source order for A(i64, text)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/enum_payload/enum_payload_boundary_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves payload ARITY and TYPES for a NAMED-payload variant B(name: text, n: i64)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
