# HIR qualified type lookup scaling Specification

> Purpose: Pin `SymbolTable.lookup_qualified_type_raw` as O(1) in the number of

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR qualified type lookup scaling Specification

Purpose: Pin `SymbolTable.lookup_qualified_type_raw` as O(1) in the number of

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HIR-QTYPEIDX-001 |
| Category | Compiler / HIR |
| Difficulty | 3/5 |
| Status | Complete |
| Research | doc/08_tracking/bug/hir_qualified_type_lookup_linear_scan_2026-08-22.md |
| Source | `test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Pin `SymbolTable.lookup_qualified_type_raw` as O(1) in the number of
qualified bindings, so HIR import lowering cannot regress to the parallel-array
linear scan that made `callable_deps` the largest exclusive term in the whole
HIR phase profile.
Audience: compiler engineers touching `src/compiler/20.hir/hir_types.spl`.

## Scenarios

### HIR qualified type lookup scaling

#### keeps a miss lookup independent of the number of qualified bindings

- Verify: keeps a miss lookup independent of the number of qualified bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps a miss lookup independent of the number of qualified bindings")
# @req: REQ-HIR-QTYPEIDX-001
val probes = 4000

var small = SymbolTable.new()
fill(small, 100)
val small_ms = miss_probe_ms(small, probes)

var large = SymbolTable.new()
fill(large, 4000)
val large_ms = miss_probe_ms(large, probes)

# 40x more bindings must not cost materially more per probe. Compare in
# integer arithmetic with a +1 floor so a sub-millisecond small side
# cannot divide by zero.
val budget = (small_ms + 1) * 3
expect(large_ms <= budget).to_be(true)
```

</details>

#### still answers hits and misses correctly at scale

- Verify: still answers hits and misses correctly at scale
   - Expected: table.lookup_qualified_type_raw("mod.pkg.m0", "Type0") equals `0`
   - Expected: table.lookup_qualified_type_raw("mod.pkg.m1999", "Type1999") equals `1999`
   - Expected: table.lookup_qualified_type_raw("mod.pkg.m1999", "Type0") equals `-1`
   - Expected: table.lookup_qualified_type_raw("nope", "Type0") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: still answers hits and misses correctly at scale")
var table = SymbolTable.new()
fill(table, 2000)
expect(table.lookup_qualified_type_raw("mod.pkg.m0", "Type0")).to_equal(0)
expect(table.lookup_qualified_type_raw("mod.pkg.m1999", "Type1999")).to_equal(1999)
expect(table.lookup_qualified_type_raw("mod.pkg.m1999", "Type0")).to_equal(-1)
expect(table.lookup_qualified_type_raw("nope", "Type0")).to_equal(-1)
```

</details>

#### keys the index injectively so a dotted split cannot alias

- Verify: keys the index injectively so a dotted split cannot alias
   - Expected: table.lookup_qualified_type_raw("a.b", "c") equals `11`
   - Expected: table.lookup_qualified_type_raw("a", "b.c") equals `22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keys the index injectively so a dotted split cannot alias")
# @req: REQ-SSPEC-LOCAL-001
# ("a.b", "c") and ("a", "b.c") both join to "a.b.c" under a `.`
# separator; the `#` key keeps them distinct.
var table = SymbolTable.new()
table.bind_qualified_type("a.b", "c", SymbolId(id: 11))
table.bind_qualified_type("a", "b.c", SymbolId(id: 22))
expect(table.lookup_qualified_type_raw("a.b", "c")).to_equal(11)
expect(table.lookup_qualified_type_raw("a", "b.c")).to_equal(22)
```

</details>

#### binds qualified functions through the same O(1) index

- Verify: binds qualified functions through the same O(1) index
   - Expected: table.lookup_qualified_function_raw("mod.m0", "fn0") equals `0`
   - Expected: table.lookup_qualified_function_raw("mod.m1999", "fn1999") equals `1999`
   - Expected: table.lookup_qualified_function_raw("mod.m1999", "fn0") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: binds qualified functions through the same O(1) index")
var table = SymbolTable.new()
var index = 0
while index < 2000:
    table.bind_qualified_function("mod.m{index}", "fn{index}", SymbolId(id: index))
    index = index + 1
expect(table.lookup_qualified_function_raw("mod.m0", "fn0")).to_equal(0)
expect(table.lookup_qualified_function_raw("mod.m1999", "fn1999")).to_equal(1999)
expect(table.lookup_qualified_function_raw("mod.m1999", "fn0")).to_equal(-1)
```

<details>
<summary>Rendered scenario source</summary>

> # @req: REQ-SSPEC-LOCAL-001<br>
> step("Verify: binds qualified functions through the same O(1) index")<br>
> var table = SymbolTable.new()<br>
> var index = 0<br>
> while index < 2000:<br>
>     table.bind_qualified_function("mod.$index$", "fn{index}", SymbolId(id: index))<br>
>     index = index + 1<br>
> expect(table.lookup_qualified_function_raw("mod.m0", "fn0")).to_equal(0)<br>
> expect(table.lookup_qualified_function_raw("mod.m1999", "fn1999")).to_equal(1999)<br>
> expect(table.lookup_qualified_function_raw("mod.m1999", "fn0")).to_equal(-1)

</details>

</details>

#### keeps the first binding when a pair is bound twice

- Verify: keeps the first binding when a pair is bound twice
   - Expected: table.lookup_qualified_type_raw("m", "T") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps the first binding when a pair is bound twice")
# @req: REQ-SSPEC-LOCAL-001
var table = SymbolTable.new()
table.bind_qualified_type("m", "T", SymbolId(id: 7))
table.bind_qualified_type("m", "T", SymbolId(id: 9))
expect(table.lookup_qualified_type_raw("m", "T")).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/hir_qualified_type_lookup_linear_scan_2026-08-22.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `52692893a03889bbdc6805ef63d7ecce353de42b60428a7e6ffabbfc3f46bf49`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52692893a03889bbdc6805ef63d7ecce353de42b60428a7e6ffabbfc3f46bf49`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52692893a03889bbdc6805ef63d7ecce353de42b60428a7e6ffabbfc3f46bf49`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **81/100**; blockers: **0**.

SSpec documentization score: 81/100
source: test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=55 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a miss lookup independent of the number of qualified bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still answers hits and misses correctly at scale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keys the index injectively so a dotted split cannot alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl. -->
