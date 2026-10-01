# Lt Gt Generic Disambiguation Specification

> Tests covering comparison chains are not misparsed as generic arguments, genuine generic instantiations still parse.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lt Gt Generic Disambiguation Specification

## Scenarios

### comparison chains are not misparsed as generic arguments

#### parses `a < 0 or b > (c)` as boolean logic, not generic args

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses `a < 0 or b > (c)` as boolean logic, not generic args


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses `a < 0 or b > (c)` as boolean logic, not generic args")
val src = "fn probe(a: i64, b: i64, c: i64) -> bool:\n" +
    "    a < 0 or b > (c)\n"
val parsed = parse_full_frontend(src, "testdata/ltgt_or_paren.spl", "ltgt_or_paren", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### parses `a < b and c > d` as boolean logic

- parses `a < b and c > d` as boolean logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses `a < b and c > d` as boolean logic")
val src = "fn probe(a: i64, b: i64, c: i64, d: i64) -> bool:\n" +
    "    a < b and c > d\n"
val parsed = parse_full_frontend(src, "testdata/ltgt_and_plain.spl", "ltgt_and_plain", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### parses `x < y or z > f(q)` where the right side is a real call

- parses `x < y or z > f(q)` where the right side is a real call


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses `x < y or z > f(q)` where the right side is a real call")
val src = "fn f(q: i64) -> i64:\n" +
    "    q\n" +
    "\n" +
    "fn probe(x: i64, y: i64, z: i64, q: i64) -> bool:\n" +
    "    x < y or z > f(q)\n"
val parsed = parse_full_frontend(src, "testdata/ltgt_or_call.spl", "ltgt_or_call", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### parses the real flat_pool_codec.spl:94 shape `if n < 0 or n > (len - pos):`

- parses the real flat_pool_codec.spl:94 shape `if n < 0 or n > (len - pos):`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the real flat_pool_codec.spl:94 shape `if n < 0 or n > (len - pos):`")
val src = "fn probe(n: i64, len: i64, pos: i64) -> bool:\n" +
    "    if n < 0 or n > (len - pos):\n" +
    "        return false\n" +
    "    true\n"
val parsed = parse_full_frontend(src, "testdata/ltgt_codec_shape.spl", "ltgt_codec_shape", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### parses `while i < n and j > (k):`

- parses `while i < n and j > (k):`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses `while i < n and j > (k):`")
val src = "fn probe(n: i64, k: i64):\n" +
    "    var i = 0\n" +
    "    var j = 0\n" +
    "    while i < n and j > (k):\n" +
    "        i = i + 1\n"
val parsed = parse_full_frontend(src, "testdata/ltgt_while.spl", "ltgt_while", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

### genuine generic instantiations still parse

#### keeps `Dict<text, i64>(...)` construction parsing

- keeps `Dict<text, i64>(...)` construction parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps `Dict<text, i64>(...)` construction parsing")
val src = "fn probe():\n" +
    "    val d = Dict<text, i64>()\n"
val parsed = parse_full_frontend(src, "testdata/gen_dict.spl", "gen_dict", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### keeps an explicit generic call `foo<i64>(x)` parsing

- keeps an explicit generic call `foo<i64>(x)` parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an explicit generic call `foo<i64>(x)` parsing")
val src = "fn foo<T>(x: T) -> T:\n" +
    "    x\n" +
    "\n" +
    "fn probe(x: i64) -> i64:\n" +
    "    foo<i64>(x)\n"
val parsed = parse_full_frontend(src, "testdata/gen_call.spl", "gen_call", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### keeps a nested generic type `List<Pair<i64, text>>` in type position parsing

- keeps a nested generic type `List<Pair<i64, text>>` in type position parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a nested generic type `List<Pair<i64, text>>` in type position parsing")
val src = "class Pair<A, B>:\n" +
    "    a: A\n" +
    "    b: B\n" +
    "\n" +
    "fn probe(xs: List<Pair<i64, text>>) -> i64:\n" +
    "    0\n"
val parsed = parse_full_frontend(src, "testdata/gen_nested.spl", "gen_nested", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### keeps `Tensor<f64>` in type position parsing

- keeps `Tensor<f64>` in type position parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps `Tensor<f64>` in type position parsing")
val src = "class Tensor<T>:\n" +
    "    n: i64\n" +
    "\n" +
    "fn probe(t: Tensor<f64>) -> i64:\n" +
    "    t.n\n"
val parsed = parse_full_frontend(src, "testdata/gen_tensor.spl", "gen_tensor", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering comparison chains are not misparsed as generic arguments, genuine generic instantiations still parse.
- comparison chains are not misparsed as generic arguments
- genuine generic instantiations still parse

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

- Canonical SPipe generation for source `b0c336dfb4d168d688fee24580214f08233b407ab8050541c7931c7cd5d2574e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b0c336dfb4d168d688fee24580214f08233b407ab8050541c7931c7cd5d2574e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b0c336dfb4d168d688fee24580214f08233b407ab8050541c7931c7cd5d2574e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses `a < 0 or b > (c)` as boolean logic, not generic args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses `a < b and c > d` as boolean logic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lt_gt_generic_disambiguation_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses `x < y or z > f(q)` where the right side is a real call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
