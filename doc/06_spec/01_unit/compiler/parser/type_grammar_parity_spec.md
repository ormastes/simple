# type_grammar_parity_spec

> Regression coverage for the compiled checker core type-grammar parity batch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# type_grammar_parity_spec

Regression coverage for the compiled checker core type-grammar parity batch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/type_grammar_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for the compiled checker core type-grammar parity batch.

## Scenarios

### compiled checker core type grammar parity

#### parses exact immutable mutable and nested reference annotations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses exact immutable mutable and nested reference annotations
   - Expected: parses_clean("type_reference_exact.spl", reference_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exact immutable mutable and nested reference annotations")
expect(parses_clean("type_reference_exact.spl", reference_source())).to_equal(true)
```

</details>

#### preserves immutable and mutable reference shapes through the flat bridge

- preserves immutable and mutable reference shapes through the flat bridge
   - Expected: is_named_reference(convert.params[0].type_.kind, "Tree", false) is true
   - Expected: mutable is true
   - Expected: parser_type_kind_named_name(element.kind) equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves immutable and mutable reference shapes through the flat bridge")
val module = parse_and_build_module(reference_source(), "type_reference_bridge.spl")
val convert = module.functions["convert"] ?? panic("missing convert")
expect(is_named_reference(convert.params[0].type_.kind, "Tree", false)).to_equal(true)
match convert.params[1].type_.kind:
    case TypeKind.Reference(inner, mutable):
        expect(mutable).to_equal(true)
        match inner.kind:
            case TypeKind.Array(element, _):
                expect(parser_type_kind_named_name(element.kind)).to_equal("u8")
            case _:
                fail("mutable reference inner type was not an array")
    case _:
        fail("mutable reference shape was not preserved")
```

</details>

#### parses the exact explicit nil return annotation

- parses the exact explicit nil return annotation
   - Expected: parses_clean("type_nil_return_exact.spl", "fn write(msg: text) -> nil:\n    nil\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the exact explicit nil return annotation")
expect(parses_clean("type_nil_return_exact.spl", "fn write(msg: text) -> nil:\n    nil\n")).to_equal(true)
```

</details>

#### parses exact and nested legacy square generic annotations

- parses exact and nested legacy square generic annotations
   - Expected: parses_clean("type_square_generic_exact.spl", legacy_generic_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exact and nested legacy square generic annotations")
expect(parses_clean("type_square_generic_exact.spl", legacy_generic_source())).to_equal(true)
```

</details>

#### keeps angle generics arrays and ordinary types adjacent

- keeps angle generics arrays and ordinary types adjacent
   - Expected: parses_clean("type_reference_adjacent.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps angle generics arrays and ordinary types adjacent")
val source = "fn adjacent(value: Result<Option<&Item>, text>, bytes: [u8]) -> bool:\n" +
    "    true\n"
expect(parses_clean("type_reference_adjacent.spl", source)).to_equal(true)
```

</details>

#### parses the exact raw pointer cast and adjacent pointer forms

- parses the exact raw pointer cast and adjacent pointer forms
   - Expected: parses_clean("type_pointer_exact.spl", pointer_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the exact raw pointer cast and adjacent pointer forms")
expect(parses_clean("type_pointer_exact.spl", pointer_source())).to_equal(true)
```

</details>

#### preserves immutable and mutable raw pointer shapes through the flat bridge

- preserves immutable and mutable raw pointer shapes through the flat bridge
   - Expected: mutable is false
   - Expected: parser_type_kind_named_name(inner.kind) equals `u8`
   - Expected: mutable is true
   - Expected: parser_type_kind_named_name(inner.kind) equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves immutable and mutable raw pointer shapes through the flat bridge")
val module = parse_and_build_module(pointer_source(), "type_pointer_bridge.spl")
val params = (module.functions["pointer_params"] ?? panic("missing pointer_params")).params
match params[0].type_.kind:
    case TypeKind.Pointer(inner, mutable):
        expect(mutable).to_equal(false)
        expect(parser_type_kind_named_name(inner.kind)).to_equal("u8")
    case _:
        fail("shared pointer shape was not preserved")
match params[2].type_.kind:
    case TypeKind.Pointer(inner, mutable):
        expect(mutable).to_equal(true)
        expect(parser_type_kind_named_name(inner.kind)).to_equal("u8")
    case _:
        fail("mutable pointer shape was not preserved")
```

</details>

#### reports a missing reference target then recovers for valid references

- reports a missing reference target then recovers for valid references
   - Expected: parses_clean("type_reference_malformed.spl", "fn bad(value: &) -> bool:\n    false\n") is false
   - Expected: parses_clean("type_reference_recovery.spl", reference_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a missing reference target then recovers for valid references")
expect(parses_clean("type_reference_malformed.spl", "fn bad(value: &) -> bool:\n    false\n")).to_equal(false)
expect(parses_clean("type_reference_recovery.spl", reference_source())).to_equal(true)
```

</details>

#### reports an unclosed square generic then recovers for a valid generic

- reports an unclosed square generic then recovers for a valid generic
   - Expected: parses_clean("type_square_generic_malformed.spl", "fn bad(value: Box[i64) -> bool:\n    false\n") is false
   - Expected: parses_clean("type_square_generic_recovery.spl", legacy_generic_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an unclosed square generic then recovers for a valid generic")
expect(parses_clean("type_square_generic_malformed.spl", "fn bad(value: Box[i64) -> bool:\n    false\n")).to_equal(false)
expect(parses_clean("type_square_generic_recovery.spl", legacy_generic_source())).to_equal(true)
```

</details>

#### reports a missing pointer target then recovers for a valid pointer cast

- reports a missing pointer target then recovers for a valid pointer cast
   - Expected: parses_clean("type_pointer_malformed.spl", "fn bad(value: *) -> bool:\n    false\n") is false
   - Expected: parses_clean("type_pointer_recovery.spl", pointer_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a missing pointer target then recovers for a valid pointer cast")
expect(parses_clean("type_pointer_malformed.spl", "fn bad(value: *) -> bool:\n    false\n")).to_equal(false)
expect(parses_clean("type_pointer_recovery.spl", pointer_source())).to_equal(true)
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

- Canonical SPipe generation for source `6b6e3a352b63ad285d28f5639270ed9791aa5aa7e7ee70e719683eef9f9693b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b6e3a352b63ad285d28f5639270ed9791aa5aa7e7ee70e719683eef9f9693b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b6e3a352b63ad285d28f5639270ed9791aa5aa7e7ee70e719683eef9f9693b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/type_grammar_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/type_grammar_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/type_grammar_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/type_grammar_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/type_grammar_parity_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses exact immutable mutable and nested reference annotations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/type_grammar_parity_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves immutable and mutable reference shapes through the flat bridge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/type_grammar_parity_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the exact explicit nil return annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
