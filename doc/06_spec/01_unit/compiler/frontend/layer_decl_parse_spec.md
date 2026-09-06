# Layer Decl Parse Specification

> Tests covering layer declaration parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Decl Parse Specification

## Scenarios

### layer declaration parsing

#### parses a bare 'layer NAME' declaration with no errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a bare 'layer NAME' declaration with no errors
   - Expected: parser_has_errors() is false
   - Expected: module.functions contains `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a bare 'layer NAME' declaration with no errors")
val source = "layer draw\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_bare.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.functions.contains("main")).to_equal(true)
```

</details>

#### parses 'layer NAME uses A, B' with no errors

- parses 'layer NAME uses A, B' with no errors
   - Expected: parser_has_errors() is false
   - Expected: module.functions contains `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses 'layer NAME uses A, B' with no errors")
val source = "layer draw\n\nlayer gui uses draw\n\nlayer web uses gui, draw\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_uses.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.functions.contains("main")).to_equal(true)
```

</details>

#### is fully inert: no stray constant/decl is emitted for the marker

- is fully inert: no stray constant/decl is emitted for the marker
   - Expected: parser_has_errors() is false
   - Expected: module.constants does not contain `_expr_layer_0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is fully inert: no stray constant/decl is emitted for the marker")
val source = "layer draw\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_inert.spl")

expect(parser_has_errors()).to_equal(false)
# The __layer_decl marker is dropped entirely by module_assembly.spl
# (mirrors __domain_block), so it must never surface as a top-level
# constant/binding under its synthetic "_expr_layer_*" name.
expect(module.constants.contains("_expr_layer_0")).to_equal(false)
```

</details>

#### sabotage: rejects a layer decl whose 'name' position holds a reserved keyword

- sabotage: rejects a layer decl whose 'name' position holds a reserved keyword
   - Expected: parser_has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sabotage: rejects a layer decl whose 'name' position holds a reserved keyword")
# "layer " is followed by whitespace + an identifier-start char ('i'),
# so current_ident_is_layer_decl() correctly enters the layer-decl
# parse path (same soft-keyword lookahead a legitimate `layer draw`
# takes) -- but the actual next token lexes as TOK_KW_IF, not
# TOK_IDENT, so parse_layer_decl's name check must reject it rather
# than silently accepting "if" as a layer name or crashing.
val source = "layer if\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_bad_name.spl")

expect(parser_has_errors()).to_equal(true)
```

</details>

#### sabotage: rejects a malformed 'uses' list (trailing comma with no name)

- sabotage: rejects a malformed 'uses' list (trailing comma with no name)
   - Expected: parser_has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sabotage: rejects a malformed 'uses' list (trailing comma with no name)")
val source = "layer draw\n\nlayer gui uses draw,\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_malformed_uses.spl")

expect(parser_has_errors()).to_equal(true)
```

</details>

#### does not regress: 'layer' still works as an ordinary field name

- does not regress: 'layer' still works as an ordinary field name
   - Expected: parser_has_errors() is false
   - Expected: module.structs contains `Binding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not regress: 'layer' still works as an ordinary field name")
# Regression guard for the soft-keyword design: `layer` must remain a
# valid plain identifier when it is NOT followed by whitespace + an
# identifier in decl-start position (e.g. as a typed struct field).
val source = "struct Binding:\n    layer: i64\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_field_regression.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.structs.contains("Binding")).to_equal(true)
```

</details>

#### wires layer/uses facts into LayerDagRegistry: accepts a valid multi-layer DAG with no diagnostic

- wires layer/uses facts into LayerDagRegistry: accepts a valid multi-layer DAG with no diagnostic
   - Expected: parser_has_errors() is false
   - Expected: module.functions contains `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires layer/uses facts into LayerDagRegistry: accepts a valid multi-layer DAG with no diagnostic")
# Distinct from the vacuous "parses with no errors" checks above (which
# would also pass if the marker were still a no-op drop): this is the
# same source as "parses 'layer NAME uses A, B' with no errors" but the
# point of this test is that check_layer_dag() actually RAN over real
# parsed facts and found them acyclic/declared-downward -- proven by
# the companion cycle test below going red on the identical wiring.
val source = "layer draw\n\nlayer gui uses draw\n\nlayer web uses gui, draw\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_dag_valid.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.functions.contains("main")).to_equal(true)
```

</details>

#### wires layer/uses facts into LayerDagRegistry: a 2-cycle produces a real compile diagnostic

- wires layer/uses facts into LayerDagRegistry: a 2-cycle produces a real compile diagnostic
   - Expected: parser_has_errors() is true
   - Expected: found_layer_dag_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires layer/uses facts into LayerDagRegistry: a 2-cycle produces a real compile diagnostic")
# End-to-end proof that module_assembly.spl's __layer_decl handling
# actually feeds a real LayerDagRegistry and calls check_layer_dag()
# -- distinct from layer_dag_checker_spec.spl, which only proves the
# standalone checker's own internal DFS/declared-upward logic against
# synthetic fixtures built directly in that spec, never through a real
# parse. If module_assembly.spl dropped the __layer_decl marker
# without wiring it (the old M0 behavior), this source would parse
# with parser_has_errors() == false, same as the acyclic case above.
val source = "layer a uses b\n\nlayer b uses a\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_dag_cycle.spl")

expect(parser_has_errors()).to_equal(true)
val errors = parser_get_errors()
var found_layer_dag_error = false
for e in errors:
    if e.contains("layer_dag"):
        found_layer_dag_error = true
expect(found_layer_dag_error).to_equal(true)
```

</details>

#### does not regress: ordinary struct/trait/module decls still parse alongside a layer decl

- does not regress: ordinary struct/trait/module decls still parse alongside a layer decl
   - Expected: parser_has_errors() is false
   - Expected: module.structs contains `Point`
   - Expected: module.traits contains `Shape`
   - Expected: module.functions contains `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not regress: ordinary struct/trait/module decls still parse alongside a layer decl")
val source = "layer draw\n\nstruct Point:\n    x: i64\n    y: i64\n\ntrait Shape:\n    fn area() -> i64\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_broader_regression.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.structs.contains("Point")).to_equal(true)
expect(module.traits.contains("Shape")).to_equal(true)
expect(module.functions.contains("main")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/layer_decl_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering layer declaration parsing.
- layer declaration parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `a36b3d8505e69f87d35c14920279f86b080ec4b14d380c9e8c0ffd83ad491385`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a36b3d8505e69f87d35c14920279f86b080ec4b14d380c9e8c0ffd83ad491385`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a36b3d8505e69f87d35c14920279f86b080ec4b14d380c9e8c0ffd83ad491385`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/layer_decl_parse_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/layer_decl_parse_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/layer_decl_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/layer_decl_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/layer_decl_parse_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a bare 'layer NAME' declaration with no errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/layer_decl_parse_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses 'layer NAME uses A, B' with no errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/layer_decl_parse_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is fully inert: no stray constant/decl is emitted for the marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
