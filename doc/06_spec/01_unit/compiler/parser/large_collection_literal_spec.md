# Parser: array and dict literals accept an unbounded number of elements

> `parse_primary_expr` in `_ParserPrimary/primary_expr.spl` used to walk the elements of an array literal with a counted `for i in 0..10000` loop, and the pairs of a dict literal with the same bound. Each pass of those loops consumes exactly one comma, so the bound capped a literal at **10000 commas**.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser: array and dict literals accept an unbounded number of elements

`parse_primary_expr` in `_ParserPrimary/primary_expr.spl` used to walk the elements of an array literal with a counted `for i in 0..10000` loop, and the pairs of a dict literal with the same bound. Each pass of those loops consumes exactly one comma, so the bound capped a literal at **10000 commas**.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax / Self-hosted frontend parity |
| Status | Active |
| Source | `test/01_unit/compiler/parser/large_collection_literal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`parse_primary_expr` in `_ParserPrimary/primary_expr.spl` used to walk the
elements of an array literal with a counted `for i in 0..10000` loop, and the
pairs of a dict literal with the same bound. Each pass of those loops consumes
exactly one comma, so the bound capped a literal at **10000 commas**.

Past the bound the loop merely fell out — it reported nothing — leaving the
cursor parked on the next comma. The `parser_expect(145)` on the following line
is what finally spoke up, and it named the token it happened to be looking at
rather than the limit that had actually been hit:

```
[parser_error] path <file> line L:C: expected ], got , ','
```

The comma it points at is perfectly well-formed, and so is every token around
it. That is what made the defect expensive to chase.

## The boundary is on commas, not elements

Because the bound counts loop passes, the element count at which a literal
breaks depends on whether it ends with a trailing comma:

| trailing comma | max elements accepted |
|----------------|-----------------------|
| yes            | 10000                 |
| no             | 10001                 |

Bisected against a stage2 self-hosted binary: a 10001-element literal *with* a
trailing comma failed while a 10001-element literal *without* one passed — same
element count, different comma count. That rules out a cap on elements stored,
and 10000 being an arbitrary decimal constant rather than a power of two rules
out an integer-width overflow or a fixed-size buffer.

The generated public-suffix table in `src/lib/common/web/public_suffix_data.spl`
tripped this at line 10012 column 25 — the comma after its 10001st entry, which
is exactly where the arithmetic predicts.

## Why the fixtures are this large

The defect is a pure *count* threshold, so the smallest witness is a literal
carrying more than 10000 commas. Both fixtures below hold 10050 elements,
packed 50 per line to keep the file short — which also demonstrates that the
threshold is not a per-line or per-token budget, since 10050 elements fit in
roughly 210 lines here versus one-per-line in the table that first tripped it.

A parse error means this file will not load at all, so the declarations are
themselves the coverage; the `it` blocks assert that every element actually
survived rather than being silently truncated.

**Note on engines:** `simple test` parses specs with the seed, which never had
the cap, so a green run here is not by itself evidence about the self-hosted
frontend. The gate that matters is the self-hosted compiler parsing this file,
which is what the bisect and the parse sweep in the bug doc measured.

## Syntax

```simple
pub val BIG_ARRAY: [i64] = [0, 1, 2, ... 10049]
pub val BIG_DICT: {i64: i64} = {0: 0, 1: 2, ... 10049: 20098}
```

## Scenarios

### large collection literals

#### keeps every element of an array literal past the old comma bound

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every element of an array literal past the old comma bound
   - Expected: BIG_ARRAY.len() equals `10050`
   - Expected: BIG_ARRAY[0] equals `0`
   - Expected: BIG_ARRAY[10000] equals `10000`
   - Expected: BIG_ARRAY[10001] equals `10001`
   - Expected: BIG_ARRAY[10049] equals `10049`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every element of an array literal past the old comma bound")
expect(BIG_ARRAY.len()).to_equal(10050)
expect(BIG_ARRAY[0]).to_equal(0)
expect(BIG_ARRAY[10000]).to_equal(10000)
expect(BIG_ARRAY[10001]).to_equal(10001)
expect(BIG_ARRAY[10049]).to_equal(10049)
```

</details>

#### keeps every pair of a dict literal past the old comma bound

- keeps every pair of a dict literal past the old comma bound
   - Expected: BIG_DICT.keys().len() equals `10050`
   - Expected: BIG_DICT[0] equals `0`
   - Expected: BIG_DICT[10000] equals `20000`
   - Expected: BIG_DICT[10001] equals `20002`
   - Expected: BIG_DICT[10049] equals `20098`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every pair of a dict literal past the old comma bound")
expect(BIG_DICT.keys().len()).to_equal(10050)
expect(BIG_DICT[0]).to_equal(0)
expect(BIG_DICT[10000]).to_equal(20000)
expect(BIG_DICT[10001]).to_equal(20002)
expect(BIG_DICT[10049]).to_equal(20098)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `cecbc854509d3d14969f0795bf693bb0c51100173d7b338d6f8295b69650e535`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cecbc854509d3d14969f0795bf693bb0c51100173d7b338d6f8295b69650e535`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cecbc854509d3d14969f0795bf693bb0c51100173d7b338d6f8295b69650e535`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/parser/large_collection_literal_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/large_collection_literal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/large_collection_literal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/large_collection_literal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/large_collection_literal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/large_collection_literal_spec.spl:489:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every element of an array literal past the old comma bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/large_collection_literal_spec.spl:498:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every pair of a dict literal past the old comma bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
