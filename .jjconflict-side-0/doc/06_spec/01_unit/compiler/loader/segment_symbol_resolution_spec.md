# Segment Symbol Resolution Specification

> Tests covering symbols resolve to correct offsets inside one mapping, POSITIVE CONTROL: the mapped code still executes correctly, bounds and lifecycle stay correct.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Segment Symbol Resolution Specification

## Scenarios

### symbols resolve to correct offsets inside one mapping

#### places each symbol at base + its segment offset

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- places each symbol at base + its segment offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places each symbol at base + its segment offset")
val mapper = mapped_trio("trio_addr")
val base = mapper.segment_base("trio_addr", 0)
assert_true(base != 0)
assert_eq(mapper.lookup("f_eleven") ?? 0, base)
assert_eq(mapper.lookup("f_twentytwo") ?? 0, base + SLOT)
assert_eq(mapper.lookup("f_thirtythree") ?? 0, base + 2 * SLOT)
```

</details>

#### gives three DISTINCT addresses from a single mapping

- gives three DISTINCT addresses from a single mapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives three DISTINCT addresses from a single mapping")
# Guards the degenerate "map once, alias everything to base" fix.
val mapper = mapped_trio("trio_distinct")
val a = mapper.lookup("f_eleven") ?? 0
val b = mapper.lookup("f_twentytwo") ?? 0
val c = mapper.lookup("f_thirtythree") ?? 0
assert_true(a != b)
assert_true(b != c)
assert_true(a != c)
assert_eq(mapper.stats().mapping_calls, 1)
```

</details>

### POSITIVE CONTROL: the mapped code still executes correctly

#### calls each symbol and gets that symbol's own value back

- calls each symbol and gets that symbol's own value back


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls each symbol and gets that symbol's own value back")
val mapper = mapped_trio("trio_exec")
# If the segment were mapped without the RW->RX transition, or the
# bytes were copied at the wrong offset, these calls would crash or
# return the wrong constant.
assert_eq(call_mapped_0(mapper.lookup("f_eleven") ?? 0), 11)
assert_eq(call_mapped_0(mapper.lookup("f_twentytwo") ?? 0), 22)
assert_eq(call_mapped_0(mapper.lookup("f_thirtythree") ?? 0), 33)
```

</details>

### bounds and lifecycle stay correct

#### refuses a symbol that does not lie inside its segment

- refuses a symbol that does not lie inside its segment


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a symbol that does not lie inside its segment")
var mapper = SegmentMapper.new()
_ = mapper.map_segment("bad", 0, three_fn_segment(), 16)
val too_far = mapper.bind_symbol("bad", 0, "outside", 24, 8)
assert_true(match too_far:
    case Ok(_): false
    case Err(_): true)
```

</details>

#### refuses a negative offset

- refuses a negative offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a negative offset")
var mapper = SegmentMapper.new()
_ = mapper.map_segment("neg", 0, three_fn_segment(), 16)
val bad = mapper.bind_symbol("neg", 0, "negative", -8, 8)
assert_true(match bad:
    case Ok(_): false
    case Err(_): true)
```

</details>

#### refuses an alignment stronger than a page

- refuses an alignment stronger than a page


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an alignment stronger than a page")
var mapper = SegmentMapper.new()
val over = mapper.map_segment("align", 0, three_fn_segment(), 65536)
assert_true(match over:
    case Ok(_): false
    case Err(_): true)
assert_eq(mapper.stats().segment_count, 0)
```

</details>

#### frees one region per segment on unmap, dropping its symbols

- frees one region per segment on unmap, dropping its symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frees one region per segment on unmap, dropping its symbols")
var mapper = SegmentMapper.new()
_ = mapper.map_segment("own", 0, three_fn_segment(), 16)
_ = mapper.map_segment("own", 1, three_fn_segment(), 16)
_ = mapper.bind_symbol("own", 0, "s0", 0, 6)
_ = mapper.bind_symbol("own", 1, "s1", 0, 6)
assert_eq(mapper.stats().segment_count, 2)
assert_eq(mapper.unmap_owner("own"), 2)
val after = mapper.stats()
assert_eq(after.segment_count, 0)
assert_eq(after.symbol_count, 0)
assert_eq(after.bytes_mapped, 0)
```

</details>

#### builds a stable segment key

- builds a stable segment key


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a stable segment key")
assert_eq(segment_key("mod", 3), "mod#3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering symbols resolve to correct offsets inside one mapping, POSITIVE CONTROL: the mapped code still executes correctly, bounds and lifecycle stay correct.
- symbols resolve to correct offsets inside one mapping
- POSITIVE CONTROL: the mapped code still executes correctly
- bounds and lifecycle stay correct

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

- Canonical SPipe generation for source `7643e96d2d1b8809150145d8c9c46ecbf33bc8e46365712bab5d56c6df9b0fed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7643e96d2d1b8809150145d8c9c46ecbf33bc8e46365712bab5d56c6df9b0fed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7643e96d2d1b8809150145d8c9c46ecbf33bc8e46365712bab5d56c6df9b0fed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/segment_symbol_resolution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/segment_symbol_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/segment_symbol_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places each symbol at base + its segment offset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives three DISTINCT addresses from a single mapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls each symbol and gets that symbol's own value back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
