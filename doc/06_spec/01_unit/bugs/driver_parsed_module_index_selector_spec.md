# Driver parsed-module index selector Specification

> Purpose: Prove that parsed-module index over the Stage 3 physical sources.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver parsed-module index selector Specification

Purpose: Prove that parsed-module index over the Stage 3 physical sources.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DRV-PARSED-MODULE-INDEX-001 |
| Category | Compiler / Driver |
| Difficulty | 4/5 |
| Status | Complete |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/bootstrap_stage3_module_surface_placeholder_nil_2026-08-01.md |
| Source | `test/01_unit/bugs/driver_parsed_module_index_selector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that parsed-module index over the Stage 3 physical sources.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### parsed-module index over the Stage 3 physical sources

#### the hir_definitions key that trapped at source index 6

#### returns the index that was inserted for hir_definitions

- returns the index that was inserted for hir_definitions
- Verify: returns the index that was inserted for hir_definitions
   - Expected: _index_lookup(ks, vs, "src/compiler/20.hir/hir_definitions.spl", cap) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns the index that was inserted for hir_definitions")
step("Verify: returns the index that was inserted for hir_definitions")
# @req: REQ-BUGS-001
# Index 6 of the source list is where Stage 3 read a nil payload.
val keys = ["src/compiler/20.hir/hir.spl",
            "src/compiler/20.hir/hir_types.spl",
            "src/compiler/20.hir/hir_expr.spl",
            "src/compiler/20.hir/hir_stmt.spl",
            "src/compiler/20.hir/hir_items.spl",
            "src/compiler/20.hir/hir_lowering/module_surface.spl",
            "src/compiler/20.hir/hir_definitions.spl",
            "src/compiler/80.driver/driver_source_loading.spl"]
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
expect(_index_lookup(ks, vs, "src/compiler/20.hir/hir_definitions.spl", cap)).to_equal(6)
```

</details>

#### returns the inserted index for every source in the set

- returns the inserted index for every source in the set
- Verify: returns the inserted index for every source in the set
   - Expected: mismatches equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns the inserted index for every source in the set")
step("Verify: returns the inserted index for every source in the set")
val keys = ["src/compiler/20.hir/hir.spl",
            "src/compiler/20.hir/hir_types.spl",
            "src/compiler/20.hir/hir_expr.spl",
            "src/compiler/20.hir/hir_stmt.spl",
            "src/compiler/20.hir/hir_items.spl",
            "src/compiler/20.hir/hir_lowering/module_surface.spl",
            "src/compiler/20.hir/hir_definitions.spl",
            "src/compiler/80.driver/driver_source_loading.spl"]
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
var mismatches = 0
var i = 0
while i < keys.len():
    if _index_lookup(ks, vs, keys[i], cap) != i:
        mismatches = mismatches + 1
    i = i + 1
expect(mismatches).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### the module-name alias that produced `missing parsed module`

#### misses fail-closed with -1 rather than a wrong index

- misses fail-closed with -1 rather than a wrong index
- Verify: misses fail-closed with -1 rather than a wrong index
   - Expected: _index_lookup(ks, vs, "compiler.hir.hir_definitions", cap) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("misses fail-closed with -1 rather than a wrong index")
step("Verify: misses fail-closed with -1 rather than a wrong index")
# `compiler.hir.hir_definitions` is a MODULE NAME, never a physical
# source key. A selector that invents an index here is exactly how
# a nil parsed module reached the surface extractor.
val keys = ["src/compiler/20.hir/hir_definitions.spl",
            "src/compiler/20.hir/hir.spl"]
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
expect(_index_lookup(ks, vs, "compiler.hir.hir_definitions", cap)).to_equal(-1)
```

</details>

#### capacity rule

#### sizes the table to 2n+1 so a free slot always remains

- sizes the table to 2n+1 so a free slot always remains
- Verify: sizes the table to 2n+1 so a free slot always remains
   - Expected: _capacity_for(8) equals `17`
   - Expected: _capacity_for(800) equals `1601`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("sizes the table to 2n+1 so a free slot always remains")
step("Verify: sizes the table to 2n+1 so a free slot always remains")
expect(_capacity_for(8)).to_equal(17)  # oracle: 17 — named expected value from the requirement
expect(_capacity_for(800)).to_equal(1601)  # oracle: 1601 — named expected value from the requirement
```

</details>

### text-keyed index selectors must return the inserted index

#### adversarial collision pressure

#### keeps every key's index correct at minimum capacity

- keeps every key's index correct at minimum capacity
- Verify: keeps every key's index correct at minimum capacity
   - Expected: mismatches equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("keeps every key's index correct at minimum capacity")
step("Verify: keeps every key's index correct at minimum capacity")
# cap = 2n+1 with n = 40 keeps load at ~0.49, so most keys probe
# past at least one occupied slot. A selector that mishandles the
# linear-probe walk returns a NEIGHBOUR's index — the original
# bug's signature — and this count goes non-zero.
var keys: [text] = []
var g = 0
while g < 40:
    keys = keys.push("src/compiler/gen/module_{g}.spl")
    g = g + 1
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
var mismatches = 0
var i = 0
while i < keys.len():
    if _index_lookup(ks, vs, keys[i], cap) != i:
        mismatches = mismatches + 1
    i = i + 1
expect(mismatches).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### never reports an index outside the inserted range

- never reports an index outside the inserted range
- Verify: never reports an index outside the inserted range
   - Expected: out_of_range equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("never reports an index outside the inserted range")
step("Verify: never reports an index outside the inserted range")
var keys: [text] = []
var g = 0
while g < 40:
    keys = keys.push("src/compiler/gen/module_{g}.spl")
    g = g + 1
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
var out_of_range = 0
var i = 0
while i < keys.len():
    val got = _index_lookup(ks, vs, keys[i], cap)
    if got < 0 or got >= keys.len():
        out_of_range = out_of_range + 1
    i = i + 1
expect(out_of_range).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### long shared-prefix keys (the real physical-path shape)

#### distinguishes paths that differ only in the last component

- distinguishes paths that differ only in the last component
- Verify: distinguishes paths that differ only in the last component
   - Expected: _index_lookup(ks, vs, keys[0], cap) equals `0`
   - Expected: _index_lookup(ks, vs, keys[1], cap) equals `1`
   - Expected: _index_lookup(ks, vs, keys[2], cap) equals `2`
   - Expected: _index_lookup(ks, vs, keys[3], cap) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("distinguishes paths that differ only in the last component")
step("Verify: distinguishes paths that differ only in the last component")
# Compiler source paths share long prefixes; a truncating or
# prefix-only hash collapses them onto one index.
val keys = ["src/compiler/20.hir/hir_lowering/_Items/a.spl",
            "src/compiler/20.hir/hir_lowering/_Items/b.spl",
            "src/compiler/20.hir/hir_lowering/_Items/c.spl",
            "src/compiler/20.hir/hir_lowering/_Items/d.spl"]
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
expect(_index_lookup(ks, vs, keys[0], cap)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(_index_lookup(ks, vs, keys[1], cap)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(_index_lookup(ks, vs, keys[2], cap)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(_index_lookup(ks, vs, keys[3], cap)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### re-inserting a key updates in place

#### does not leak a stale duplicate slot

- does not leak a stale duplicate slot
- Verify: does not leak a stale duplicate slot
   - Expected: _index_lookup(ks, vs, "a.spl", cap) equals `2`
   - Expected: _index_lookup(ks, vs, "b.spl", cap) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("does not leak a stale duplicate slot")
step("Verify: does not leak a stale duplicate slot")
# An alias re-registering the same physical source must overwrite,
# not append a second slot that a later lookup could reach first.
val keys = ["a.spl", "b.spl", "a.spl"]
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
expect(_index_lookup(ks, vs, "a.spl", cap)).to_equal(2)
expect(_index_lookup(ks, vs, "b.spl", cap)).to_equal(1)
```

</details>

#### cross-check against Dict<text, i64>

#### agrees with the array selector on every key

- agrees with the array selector on every key
- Verify: agrees with the array selector on every key
   - Expected: disagreements equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("agrees with the array selector on every key")
step("Verify: agrees with the array selector on every key")
# This is the exact comparison the pre-fix code failed: the Dict
# answered with an incorrect index while the parallel-array
# selector was right. Any engine on which text-keyed Dict lookup
# disagrees with the oracle reds here.
var keys: [text] = []
var g = 0
while g < 24:
    keys = keys.push("src/compiler/gen/dictcheck_{g}.spl")
    g = g + 1
val cap = _capacity_for(keys.len())
val (ks, vs) = _index_build(keys, cap)
var d: Dict<text, i64> = {}
var i = 0
while i < keys.len():
    d[keys[i]] = i
    i = i + 1
var disagreements = 0
i = 0
while i < keys.len():
    if d.get(keys[i]) != _index_lookup(ks, vs, keys[i], cap):
        disagreements = disagreements + 1
    i = i + 1
expect(disagreements).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### parsed-module index spec vacuity guard

#### vacuity probe

#### executes assertions in this file

- executes assertions in this file
- Verify: executes assertions in this file
   - Expected: _index_lookup(ks, vs, "vacuity.spl", cap) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("executes assertions in this file")
step("Verify: executes assertions in this file")
val cap = _capacity_for(1)
val (ks, vs) = _index_build(["vacuity.spl"], cap)
expect(_index_lookup(ks, vs, "vacuity.spl", cap)).to_equal(0)
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


## Related Documentation

- **Research:** `doc/08_tracking/bug/bootstrap_stage3_module_surface_placeholder_nil_2026-08-01.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BUGS`
- `REQ-BUGS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99b987d020c38741e028b658c55894b761f193e409ce27c5fd4b540bcf19283c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99b987d020c38741e028b658c55894b761f193e409ce27c5fd4b540bcf19283c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99b987d020c38741e028b658c55894b761f193e409ce27c5fd4b540bcf19283c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/bugs/driver_parsed_module_index_selector_spec.spl
mirror: doc/06_spec/01_unit/bugs/driver_parsed_module_index_selector_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/driver_parsed_module_index_selector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/driver_parsed_module_index_selector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/driver_parsed_module_index_selector_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/bugs/driver_parsed_module_index_selector_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the index that was inserted for hir_definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/driver_parsed_module_index_selector_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the inserted index for every source in the set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/driver_parsed_module_index_selector_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'misses fail-closed with -1 rather than a wrong index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
