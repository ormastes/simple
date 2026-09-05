# Enum Bare Name Collision Loud Miss Specification

> Tests covering enum bare-name collision produces a loud miss, the MIR construction sites emit the miss instead of swallowing it, interpreter enum table reports the same collision.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Bare Name Collision Loud Miss Specification

## Scenarios

### enum bare-name collision produces a loud miss

#### records a divergent same-bare-name registration and names both sides

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records a divergent same-bare-name registration and names both sides
   - Expected: lowering.enum_bare_name_collisions.has("Style") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records a divergent same-bare-name registration and names both sides")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic"]))
# A DIFFERENT enum sharing the bare name evicts the first one.
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

expect(lowering.enum_bare_name_collisions.has("Style")).to_equal(true)
val recorded = lowering.enum_bare_name_collisions["Style"]
expect(recorded).to_contain("Bold, Italic")
expect(recorded).to_contain("Plain, Reverse")
expect(recorded).to_contain("term.render.Style")
```

</details>

#### stays quiet when the same enum is re-registered identically

- stays quiet when the same enum is re-registered identically
   - Expected: lowering.enum_bare_name_collisions.has("Colour") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays quiet when the same enum is re-registered identically")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Colour", "ui.Colour", ["Red", "Green"]))
lowering.register_enum_variants(make_enum(
    "Colour", "ui.Colour", ["Red", "Green"]))

expect(lowering.enum_bare_name_collisions.has("Colour")).to_equal(false)
```

</details>

#### reports a variant that survived eviction as a -1 miss

- reports a variant that survived eviction as a -1 miss
   - Expected: lowering.enum_variant_discriminant("Style", "Bold") equals `-1`
   - Expected: lowering.enum_variant_discriminant("Style", "Plain") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a variant that survived eviction as a -1 miss")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

# "Bold" belonged to the evicted enum, so the bare-keyed lookup misses.
expect(lowering.enum_variant_discriminant("Style", "Bold")).to_equal(-1)
# The surviving registration still resolves.
expect(lowering.enum_variant_discriminant("Style", "Plain")).to_equal(0)
```

</details>

#### names the colliding owner in the miss detail

- names the colliding owner in the miss detail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the colliding owner in the miss detail")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

val detail = lowering.enum_variant_miss_detail("Style", "Bold")
expect(detail).to_contain("MORE THAN ONE")
expect(detail).to_contain("Style")
expect(detail).to_contain("Bold, Italic")
```

</details>

#### names any other registered enum that does declare the variant

- names any other registered enum that does declare the variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names any other registered enum that does declare the variant")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Shape", "geom.Shape", ["Circle", "Square"]))
lowering.register_enum_variants(make_enum(
    "Widget", "ui.Widget", ["Button", "Slider"]))

# `Widget` has no `Circle`; the detail must point at `Shape`.
val detail = lowering.enum_variant_miss_detail("Widget", "Circle")
expect(detail).to_contain("Circle")
expect(detail).to_contain("Shape")
```

</details>

#### falls back to listing the registered variants when nothing collides

- falls back to listing the registered variants when nothing collides


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("falls back to listing the registered variants when nothing collides")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Shape", "geom.Shape", ["Circle", "Square"]))

val detail = lowering.enum_variant_miss_detail("Shape", "Hexagon")
expect(detail).to_contain("Circle, Square")
```

</details>

### the MIR construction sites emit the miss instead of swallowing it

#### records a loud error when a construction resolves to discriminant -1

- records a loud error when a construction resolves to discriminant -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records a loud error when a construction resolves to discriminant -1")
var lowering = MirLowering.new(SymbolTable.new())
val web_style = make_enum("Style", "web.layout.Style", ["Bold", "Italic"])
val term_style = make_enum("Style", "term.render.Style", ["Plain", "Reverse"])
lowering.register_enum_variants(web_style)
lowering.register_enum_runtime_id(web_style)
lowering.register_enum_variants(term_style)
lowering.register_enum_runtime_id(term_style)

var builder = lowering.builder
builder.begin_function(SymbolId(id: 7100), "ctor_probe", MirSignature(
    params: [], return_type: MirType.unit(), is_variadic: false), Span.empty())
lowering.builder = builder

val before = lowering.errors.len()
# `Bold` belonged to the evicted declaration. This used to emit -1 as
# the discriminant constant with NO diagnostic whatsoever.
lowering.lower_enum_construct_named("Style", "Bold", [])
expect(lowering.errors.len()).to_be_greater_than(before)

val message = lowering.errors[lowering.errors.len() - 1].message
expect(message).to_contain("enum variant lookup miss")
expect(message).to_contain("Style")
expect(message).to_contain("Bold")
# The colliding owner must be named, not just the failure.
expect(message).to_contain("MORE THAN ONE")
```

</details>

#### stays quiet when the variant resolves normally

- stays quiet when the variant resolves normally
   - Expected: lowering.errors.len() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays quiet when the variant resolves normally")
var lowering = MirLowering.new(SymbolTable.new())
val shape = make_enum("Shape", "geom.Shape", ["Circle", "Square"])
lowering.register_enum_variants(shape)
lowering.register_enum_runtime_id(shape)

var builder = lowering.builder
builder.begin_function(SymbolId(id: 7101), "ok_probe", MirSignature(
    params: [], return_type: MirType.unit(), is_variadic: false), Span.empty())
lowering.builder = builder

val before = lowering.errors.len()
lowering.lower_enum_construct_named("Shape", "Circle", [])
expect(lowering.errors.len()).to_equal(before)
```

</details>

### interpreter enum table reports the same collision

#### drops the second divergent declaration (first-wins) rather than merging

- drops the second divergent declaration (first-wins) rather than merging
   - Expected: enum_table_lookup("Style") equals `Bold,Italic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("drops the second divergent declaration (first-wins) rather than merging")
enum_table_reset()
enum_table_register("Style", ["Bold", "Italic"])
enum_table_register("Style", ["Plain", "Reverse"])

# First-wins: the SECOND declaration is discarded entirely, and the
# variant sets are NOT merged. A `case Plain:` arm therefore matches
# nothing at all under the interpreter.
expect(enum_table_lookup("Style")).to_equal("Bold,Italic")
```

</details>

#### keeps an identical re-registration idempotent

- keeps an identical re-registration idempotent
   - Expected: enum_table_lookup("Colour") equals `Red,Green`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps an identical re-registration idempotent")
enum_table_reset()
enum_table_register("Colour", ["Red", "Green"])
enum_table_register("Colour", ["Red", "Green"])

expect(enum_table_lookup("Colour")).to_equal("Red,Green")
```

</details>

#### warns loudly on the divergent drop instead of returning silently

- warns loudly on the divergent drop instead of returning silently


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns loudly on the divergent drop instead of returning silently")
# The drop itself is unobservable from outside the table (that is the
# whole defect), so pin the warning at the source. The registration path
# must consult the collision reporter BEFORE its early return.
val tables = read_source(
    "src/compiler/10.frontend/core/interpreter/eval_tables.spl")

expect(tables).to_contain(
    "_enum_warn_bare_name_collision(name, enum_reg_variants[idx], variants.join(\",\"))")
expect(tables).to_contain("compiler_enum_bare_name_collision")
# Divergence-gated: identical re-registrations must stay quiet.
expect(tables).to_contain("if existing_csv == new_csv:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering enum bare-name collision produces a loud miss, the MIR construction sites emit the miss instead of swallowing it, interpreter enum table reports the same collision.
- enum bare-name collision produces a loud miss
- the MIR construction sites emit the miss instead of swallowing it
- interpreter enum table reports the same collision

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `4d71b3598336f372af10314975827b1b24d317b7e5ee9e90d555eecd7c9504ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d71b3598336f372af10314975827b1b24d317b7e5ee9e90d555eecd7c9504ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d71b3598336f372af10314975827b1b24d317b7e5ee9e90d555eecd7c9504ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a divergent same-bare-name registration and names both sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays quiet when the same enum is re-registered identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a variant that survived eviction as a -1 miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
