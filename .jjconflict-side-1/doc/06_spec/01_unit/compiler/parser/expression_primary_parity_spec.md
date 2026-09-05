# expression_primary_parity_spec

> Compiled-checker expression/primary parser parity regressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expression_primary_parity_spec

Compiled-checker expression/primary parser parity regressions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/expression_primary_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Compiled-checker expression/primary parser parity regressions.

## Scenarios

### compiled checker expression and primary parity

#### accepts exact pass-named constructor arguments and adjacent keywords

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts exact pass-named constructor arguments and adjacent keywords
   - Expected: parses_clean("keyword_named_args_exact.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts exact pass-named constructor arguments and adjacent keywords")
val source = "struct Evidence:\n" +
    "    pass: bool\n" +
    "    type: text\n" +
    "fn make() -> Evidence:\n" +
    "    Evidence(pass: true, type: \"smoke\")\n"
expect(parses_clean("keyword_named_args_exact.spl", source)).to_equal(true)
```

</details>

#### diagnoses a missing named-argument colon then recovers

- diagnoses a missing named-argument colon then recovers
   - Expected: parses_clean("keyword_named_args_bad.spl", "fn bad():\n    Evidence(pass true)\n") is false
   - Expected: parses_clean("keyword_named_args_recovery.spl", "fn good():\n    Evidence(pass: true)\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("diagnoses a missing named-argument colon then recovers")
expect(parses_clean("keyword_named_args_bad.spl", "fn bad():\n    Evidence(pass true)\n")).to_equal(false)
expect(parses_clean("keyword_named_args_recovery.spl", "fn good():\n    Evidence(pass: true)\n")).to_equal(true)
```

</details>

#### preserves exact and nested pointer dereference as real unary nodes

- preserves exact and nested pointer dereference as real unary nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves exact and nested pointer dereference as real unary nodes")
val expr = first_expr("fn deref(ptr: *u64) -> u64:\n    *(*ptr)\n", "deref")
match expr.kind:
    case ExprKind.Unary(UnaryOp.Deref, inner):
        match inner.kind:
            case ExprKind.Unary(UnaryOp.Deref, _): pass
            case _: fail("inner pointer dereference was not preserved")
    case _:
        fail("pointer dereference was not preserved")
```

</details>

#### diagnoses a missing dereference operand then recovers

- diagnoses a missing dereference operand then recovers
   - Expected: parses_clean("deref_bad.spl", "fn bad(ptr: *u64):\n    *\n") is false
   - Expected: parses_clean("deref_recovery.spl", "fn good(ptr: *u64):\n    *ptr\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("diagnoses a missing dereference operand then recovers")
expect(parses_clean("deref_bad.spl", "fn bad(ptr: *u64):\n    *\n")).to_equal(false)
expect(parses_clean("deref_recovery.spl", "fn good(ptr: *u64):\n    *ptr\n")).to_equal(true)
```

</details>

#### preserves exact is-type syntax as the canonical binary operator

- preserves exact is-type syntax as the canonical binary operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves exact is-type syntax as the canonical binary operator")
val expr = first_expr("fn type_test(value: Any) -> bool:\n    value is i64\n", "type_test")
match expr.kind:
    case ExprKind.Binary(op, _, _): expect(op).to_equal(BinOp.Is)
    case _: fail("is type-test was not preserved as a binary expression")
```

</details>

#### diagnoses a missing is operand then recovers in a call argument

- diagnoses a missing is operand then recovers in a call argument
   - Expected: parses_clean("is_bad.spl", "fn bad(value: Any):\n    value is\n") is false
   - Expected: parses_clean("is_recovery.spl", "fn good(value: Any):\n    consume(value is i64)\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("diagnoses a missing is operand then recovers in a call argument")
expect(parses_clean("is_bad.spl", "fn bad(value: Any):\n    value is\n")).to_equal(false)
expect(parses_clean("is_recovery.spl", "fn good(value: Any):\n    consume(value is i64)\n")).to_equal(true)
```

</details>

#### preserves exact image and adjacent nested custom-block payloads

- preserves exact image and adjacent nested custom-block payloads
   - Expected: kind equals `img`
   - Expected: parses_clean("custom_nested.spl", "fn query():\n    sql{select {nested} from t}\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves exact image and adjacent nested custom-block payloads")
val image = first_expr("fn image():\n    val hero = img{\"hero.svg\"}\n", "image")
match image.kind:
    case ExprKind.CustomBlock(kind, value):
        expect(kind).to_equal("img")
        match value:
            case BlockValue.Raw(payload): expect(payload).to_equal("\"hero.svg\"")
            case _: fail("image custom block did not retain raw payload")
    case _: fail("image custom block did not reach the canonical expression kind")
expect(parses_clean("custom_nested.spl", "fn query():\n    sql{select {nested} from t}\n")).to_equal(true)
```

</details>

#### diagnoses an unterminated custom block then recovers

- diagnoses an unterminated custom block then recovers
   - Expected: parses_clean("custom_bad.spl", "fn bad():\n    img{\"open.svg\"\n") is false
   - Expected: parses_clean("custom_recovery.spl", "fn good():\n    img{\"closed.svg\"}\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("diagnoses an unterminated custom block then recovers")
expect(parses_clean("custom_bad.spl", "fn bad():\n    img{\"open.svg\"\n")).to_equal(false)
expect(parses_clean("custom_recovery.spl", "fn good():\n    img{\"closed.svg\"}\n")).to_equal(true)
```

</details>

#### keeps textual xor callable and caret xor binary

- keeps textual xor callable and caret xor binary
   - Expected: parses_clean("xor_call_exact.spl", "fn compare(a: i64, b: i64):\n    xor(a, b)\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps textual xor callable and caret xor binary")
expect(parses_clean("xor_call_exact.spl", "fn compare(a: i64, b: i64):\n    xor(a, b)\n")).to_equal(true)
val expr = first_expr("fn bitxor(a: i64, b: i64):\n    a ^ b\n", "bitxor")
match expr.kind:
    case ExprKind.Binary(op, _, _): expect(op).to_equal(BinOp.BitXor)
    case _: fail("caret xor did not remain a binary expression")
```

</details>

#### diagnoses an incomplete xor call then recovers

- diagnoses an incomplete xor call then recovers
   - Expected: parses_clean("xor_bad.spl", "fn bad(a: i64):\n    xor(a,\n") is false
   - Expected: parses_clean("xor_recovery.spl", "fn good(a: i64):\n    xor(a, 1)\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("diagnoses an incomplete xor call then recovers")
expect(parses_clean("xor_bad.spl", "fn bad(a: i64):\n    xor(a,\n")).to_equal(false)
expect(parses_clean("xor_recovery.spl", "fn good(a: i64):\n    xor(a, 1)\n")).to_equal(true)
```

</details>

#### preserves unsafe and adjacent danger blocks

- preserves unsafe and adjacent danger blocks
   - Expected: parses_clean("unsafe_exact_adjacent.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves unsafe and adjacent danger blocks")
val source = "fn unsafe_probe():\n" +
    "    unsafe:\n" +
    "        val value = 1\n" +
    "    danger:\n" +
    "        val other = 2\n"
expect(parses_clean("unsafe_exact_adjacent.spl", source)).to_equal(true)
```

</details>

#### diagnoses a malformed unsafe body then recovers

- diagnoses a malformed unsafe body then recovers
   - Expected: parses_clean("unsafe_bad.spl", "fn bad():\n    unsafe:\n        +\n") is false
   - Expected: parses_clean("unsafe_recovery.spl", "fn good():\n    unsafe:\n        pass\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("diagnoses a malformed unsafe body then recovers")
expect(parses_clean("unsafe_bad.spl", "fn bad():\n    unsafe:\n        +\n")).to_equal(false)
expect(parses_clean("unsafe_recovery.spl", "fn good():\n    unsafe:\n        pass\n")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `60d51c87186925608c0aeb58ff71bb520a18495a8758085f7dba43c490449fd6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60d51c87186925608c0aeb58ff71bb520a18495a8758085f7dba43c490449fd6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60d51c87186925608c0aeb58ff71bb520a18495a8758085f7dba43c490449fd6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/expression_primary_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/expression_primary_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/expression_primary_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/expression_primary_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/expression_primary_parity_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves exact and nested pointer dereference as real unary nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/expression_primary_parity_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diagnoses a missing dereference operand then recovers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/expression_primary_parity_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves exact is-type syntax as the canonical binary operator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
