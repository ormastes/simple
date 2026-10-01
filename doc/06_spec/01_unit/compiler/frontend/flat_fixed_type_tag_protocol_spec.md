# Flat Fixed Type Tag Protocol Specification

> Tests covering compiled flat fixed type tag protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Fixed Type Tag Protocol Specification

## Scenarios

### compiled flat fixed type tag protocol

#### keeps parser tags and rich return types distinct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps parser tags and rich return types distinct
   - Expected: raw_return_tag("flag") equals `1`
   - Expected: raw_return_tag("word") equals `4`
   - Expected: raw_return_tag("ints") equals `5`
   - Expected: raw_return_tag("words") equals `6`
   - Expected: raw_return_tag("u8_value") equals `27`
   - Expected: raw_return_tag("u16_value") equals `28`
   - Expected: raw_return_tag("u32_value") equals `29`
   - Expected: raw_return_tag("u64_value") equals `30`
   - Expected: raw_return_tag("i8_value") equals `31`
   - Expected: raw_return_tag("i16_value") equals `32`
   - Expected: raw_return_tag("i32_value") equals `33`
   - Expected: parser_type_kind_named_name(flag.return_type.kind) equals `bool`
   - Expected: parser_type_kind_named_name(word.return_type.kind) equals `text`
   - Expected: array_element_name(ints.return_type.kind) equals `i64`
   - Expected: array_element_name(words.return_type.kind) equals `text`
   - Expected: parser_type_kind_named_name((module.functions["u8_value"] ?? panic("missing u8")).return_type.kind) equals `u8`
   - Expected: parser_type_kind_named_name((module.functions["u16_value"] ?? panic("missing u16")).return_type.kind) equals `u16`
   - Expected: parser_type_kind_named_name((module.functions["u32_value"] ?? panic("missing u32")).return_type.kind) equals `u32`
   - Expected: parser_type_kind_named_name((module.functions["u64_value"] ?? panic("missing u64")).return_type.kind) equals `u64`
   - Expected: parser_type_kind_named_name((module.functions["i8_value"] ?? panic("missing i8")).return_type.kind) equals `i8`
   - Expected: parser_type_kind_named_name((module.functions["i16_value"] ?? panic("missing i16")).return_type.kind) equals `i16`
   - Expected: parser_type_kind_named_name((module.functions["i32_value"] ?? panic("missing i32")).return_type.kind) equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps parser tags and rich return types distinct")
val source = "fn flag() -> bool:\n    true\n\nfn word() -> text:\n    \"ok\"\n\nfn ints() -> [i64]:\n    [2, 3]\n\nfn words() -> [text]:\n    [\"o\", \"k\"]\n\nfn u8_value() -> u8:\n    1\n\nfn u16_value() -> u16:\n    2\n\nfn u32_value() -> u32:\n    3\n\nfn u64_value() -> u64:\n    4\n\nfn i8_value() -> i8:\n    5\n\nfn i16_value() -> i16:\n    6\n\nfn i32_value() -> i32:\n    7\n"
val module = parse_and_build_module(source, "flat_fixed_type_tag_protocol.spl")

expect(raw_return_tag("flag")).to_equal(1)
expect(raw_return_tag("word")).to_equal(4)
expect(raw_return_tag("ints")).to_equal(5)
expect(raw_return_tag("words")).to_equal(6)
expect(raw_return_tag("u8_value")).to_equal(27)
expect(raw_return_tag("u16_value")).to_equal(28)
expect(raw_return_tag("u32_value")).to_equal(29)
expect(raw_return_tag("u64_value")).to_equal(30)
expect(raw_return_tag("i8_value")).to_equal(31)
expect(raw_return_tag("i16_value")).to_equal(32)
expect(raw_return_tag("i32_value")).to_equal(33)

val flag = module.functions["flag"] ?? panic("missing flag")
val word = module.functions["word"] ?? panic("missing word")
val ints = module.functions["ints"] ?? panic("missing ints")
val words = module.functions["words"] ?? panic("missing words")
expect(parser_type_kind_named_name(flag.return_type.kind)).to_equal("bool")
expect(parser_type_kind_named_name(word.return_type.kind)).to_equal("text")
expect(array_element_name(ints.return_type.kind)).to_equal("i64")
expect(array_element_name(words.return_type.kind)).to_equal("text")
expect(parser_type_kind_named_name((module.functions["u8_value"] ?? panic("missing u8")).return_type.kind)).to_equal("u8")
expect(parser_type_kind_named_name((module.functions["u16_value"] ?? panic("missing u16")).return_type.kind)).to_equal("u16")
expect(parser_type_kind_named_name((module.functions["u32_value"] ?? panic("missing u32")).return_type.kind)).to_equal("u32")
expect(parser_type_kind_named_name((module.functions["u64_value"] ?? panic("missing u64")).return_type.kind)).to_equal("u64")
expect(parser_type_kind_named_name((module.functions["i8_value"] ?? panic("missing i8")).return_type.kind)).to_equal("i8")
expect(parser_type_kind_named_name((module.functions["i16_value"] ?? panic("missing i16")).return_type.kind)).to_equal("i16")
expect(parser_type_kind_named_name((module.functions["i32_value"] ?? panic("missing i32")).return_type.kind)).to_equal("i32")
```

</details>

#### guards expression arena access behind the literal tag hole

- guards expression arena access behind the literal tag hole


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guards expression arena access behind the literal tag hole")
val source = file_read("src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl")
expect(source).to_contain("if type_expr_idx < 34 or type_expr_idx >= 500 or type_expr_idx >= expr_count():")
```

</details>

#### converts typed extern and ordinary parameters through stable Type locals

- converts typed extern and ordinary parameters through stable Type locals
   - Expected: parser_type_kind_named_name(external.params[0].type_.kind) equals `text`
   - Expected: array_element_name(external.params[1].type_.kind) equals `text`
   - Expected: parser_type_kind_named_name(local.params[0].type_.kind) equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts typed extern and ordinary parameters through stable Type locals")
val source = "extern fn bridge_probe(path: text, args: [text]) -> bool\n\nfn local_probe(value: text = \"ok\") -> text:\n    value\n"
val module = parse_and_build_module(source, "flat_param_type_transport.spl")
val external = module.functions["bridge_probe"] ?? panic("missing extern")
val local = module.functions["local_probe"] ?? panic("missing local")
expect(parser_type_kind_named_name(external.params[0].type_.kind)).to_equal("text")
expect(array_element_name(external.params[1].type_.kind)).to_equal("text")
expect(parser_type_kind_named_name(local.params[0].type_.kind)).to_equal("text")
expect(local.params[0].has_default).to_be(true)
```

</details>

#### forbids inline rich aggregate selection in Param constructors

- forbids inline rich aggregate selection in Param constructors


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("forbids inline rich aggregate selection in Param constructors")
val source = file_read("src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl")
expect(source).to_contain("var param_type: Type = Type(kind: TypeKind.Infer, span: span)")
expect(source).to_contain("var param_default: Expr = Expr(kind: ExprKind.NilLit, span: span)")
expect(source).to_contain("var inferred_ret: Type = Type(kind: TypeKind.Infer, span: span)")
expect(source).to_contain("var extern_inferred_ret: Type = Type(kind: TypeKind.Infer, span: span)")
expect(source.contains("type_: if has_t:")).to_be(false)
expect(source.contains("default: if p_has_default:")).to_be(false)
expect(source.contains("if has_ret: convert_flat_type(ret) else:")).to_be(false)
expect(source.contains("if extern_has_ret: convert_flat_type(ret) else:")).to_be(false)
```

</details>

#### rebuilds enum spans after declaration-walk safepoints

- rebuilds enum spans after declaration-walk safepoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rebuilds enum spans after declaration-walk safepoints")
val source = file_read("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl")
expect(source).to_contain("var e_discriminant = Expr(kind: ExprKind.NilLit, span: make_span())")
expect(source).to_contain("default: Type(kind: TypeKind.Infer, span: make_span())")
```

</details>

#### converts standalone flat block expressions

- converts standalone flat block expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts standalone flat block expressions")
val source = file_read("src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl")
expect(source).to_contain("if tag == EXPR_BLOCK:")
expect(source).to_contain("ExprKind.Block(flat_if_branch_block(idx, span))")
expect(source).to_contain("val tail_idx = expr_get_left(branch_idx)")
expect(source).to_contain("convert_flat_stmt_in_list(b_stmts[bi], false)")
```

</details>

#### re-roots resolved field types before HIR aggregate construction

- re-roots resolved field types before HIR aggregate construction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("re-roots resolved field types before HIR aggregate construction")
val source = file_read("src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl")
expect(source).to_contain("val live_field_type = HirType(")
expect(source).to_contain("type_: live_field_type")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compiled flat fixed type tag protocol.
- compiled flat fixed type tag protocol

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

- Canonical SPipe generation for source `fdee067a51a0a0a641f962b210d0ca11a73ea676395324cbcd65fa8da6838432`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdee067a51a0a0a641f962b210d0ca11a73ea676395324cbcd65fa8da6838432`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdee067a51a0a0a641f962b210d0ca11a73ea676395324cbcd65fa8da6838432`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps parser tags and rich return types distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards expression arena access behind the literal tag hole' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts typed extern and ordinary parameters through stable Type locals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
