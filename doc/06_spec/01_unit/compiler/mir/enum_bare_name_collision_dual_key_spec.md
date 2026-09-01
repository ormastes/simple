# enum_bare_name_collision_dual_key_spec

> Purpose: Prove that the qualified keyspace retains every declaration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# enum_bare_name_collision_dual_key_spec

Purpose: Prove that the qualified keyspace retains every declaration.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that the qualified keyspace retains every declaration.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### the qualified keyspace retains every declaration

#### keeps BOTH sides of a divergent bare-name contest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps BOTH sides of a divergent bare-name contest
- Verify: keeps BOTH sides of a divergent bare-name contest
   - Expected: lowering.enum_variant_index.has("Style") is true
   - Expected: lowering.enum_variant_index_q.has("web.layout.Style") is true
   - Expected: lowering.enum_variant_index_q.has("term.render.Style") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps BOTH sides of a divergent bare-name contest")
step("Verify: keeps BOTH sides of a divergent bare-name contest")
# @req: REQ-COMPILER-MIR-001
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic", "Underline"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

# The BARE map is still last-wins -- unchanged, on purpose.
expect(lowering.enum_variant_index.has("Style")).to_equal(true)
# The QUALIFIED map holds one entry per declaration; nothing evicted.
expect(lowering.enum_variant_index_q.has("web.layout.Style")).to_equal(true)
expect(lowering.enum_variant_index_q.has("term.render.Style")).to_equal(true)
```

</details>

#### resolves the EVICTED enum's variant through its runtime_name

- resolves the EVICTED enum's variant through its runtime_name
- Verify: resolves the EVICTED enum's variant through its runtime_name
   - Expected: lowering.enum_variant_discriminant("Style", "Bold") equals `-1`
   - Expected: lowering.enum_variant_discriminant("Style", "Underline") equals `-1`
   - Expected: lowering.enum_variant_discriminant("web.layout.Style", "Bold") equals `0`
   - Expected: lowering.enum_variant_discriminant("web.layout.Style", "Italic") equals `1`
   - Expected: lowering.enum_variant_discriminant("web.layout.Style", "Underline") equals `2`
   - Expected: lowering.enum_variant_discriminant("term.render.Style", "Reverse") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the EVICTED enum's variant through its runtime_name")
step("Verify: resolves the EVICTED enum's variant through its runtime_name")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic", "Underline"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

# TRUE-POSITIVE CONTROL, MIR surface. The bare lookup must STILL miss in
# this same object: that is what proves the qualified hit below is a
# genuinely new capability and not the bare map quietly answering.
expect(lowering.enum_variant_discriminant("Style", "Bold")).to_equal(-1)
expect(lowering.enum_variant_discriminant("Style", "Underline")).to_equal(-1)

# Hand-computed from the declared order ["Bold","Italic","Underline"].
expect(lowering.enum_variant_discriminant("web.layout.Style", "Bold")).to_equal(0)
expect(lowering.enum_variant_discriminant("web.layout.Style", "Italic")).to_equal(1)
expect(lowering.enum_variant_discriminant("web.layout.Style", "Underline")).to_equal(2)
# And the survivor still resolves under its own runtime_name.
expect(lowering.enum_variant_discriminant("term.render.Style", "Reverse")).to_equal(1)
```

</details>

#### does NOT let the bare map rescue a genuine qualified miss

- does NOT let the bare map rescue a genuine qualified miss
- Verify: does NOT let the bare map rescue a genuine qualified miss
   - Expected: lowering.enum_variant_discriminant("web.layout.Style", "Plain") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does NOT let the bare map rescue a genuine qualified miss")
step("Verify: does NOT let the bare map rescue a genuine qualified miss")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic", "Underline"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

# `Plain` is declared by term.render.Style, NOT by web.layout.Style.
# A qualified lookup that fell back to the bare (last-wins = term) map
# on a -1 would answer 0 here -- silently borrowing another enum's
# discriminant, exactly the defect being fixed. It must stay a miss.
expect(lowering.enum_variant_discriminant("web.layout.Style", "Plain")).to_equal(-1)
```

</details>

#### raises the ambiguity flag only on DIVERGENCE

- raises the ambiguity flag only on DIVERGENCE
- Verify: raises the ambiguity flag only on DIVERGENCE
   - Expected: lowering.enum_bare_ambiguous.has("Style") is true
   - Expected: lowering.enum_bare_ambiguous.has("Colour") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("raises the ambiguity flag only on DIVERGENCE")
step("Verify: raises the ambiguity flag only on DIVERGENCE")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))
lowering.register_enum_variants(make_enum(
    "Colour", "ui.a.Colour", ["Red", "Green"]))
lowering.register_enum_variants(make_enum(
    "Colour", "ui.b.Colour", ["Red", "Green"]))

expect(lowering.enum_bare_ambiguous.has("Style")).to_equal(true)
# Identical variant sets are the 192 benign duplicates; they must not
# be flagged, or the flag is useless noise.
expect(lowering.enum_bare_ambiguous.has("Colour")).to_equal(false)
```

</details>

#### maps every runtime_name back to its bare name

- maps every runtime_name back to its bare name
- Verify: maps every runtime_name back to its bare name
   - Expected: lowering.enum_bare_of("web.layout.Style") equals `Style`
   - Expected: lowering.enum_bare_of("Style") equals `Style`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps every runtime_name back to its bare name")
step("Verify: maps every runtime_name back to its bare name")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic"]))

expect(lowering.enum_bare_of("web.layout.Style")).to_equal("Style")
# An unknown key passes through unchanged, so a bare name stays bare.
expect(lowering.enum_bare_of("Style")).to_equal("Style")
```

</details>

### the owner-search scans count over the qualified keyspace

#### counts two owners where the bare map showed one

- counts two owners where the bare map showed one
- Verify: counts two owners where the bare map showed one
   - Expected: lowering.enum_variant_index.has("Kind") is true
   - Expected: lowering.enum_variant_discriminant("parser.Kind", "Atom") equals `0`
   - Expected: lowering.enum_variant_discriminant("render.Kind", "Atom") equals `1`
   - Expected: lowering.variant_owner_keys("Atom").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts two owners where the bare map showed one")
step("Verify: counts two owners where the bare map showed one")
var lowering = MirLowering.new(SymbolTable.new())
# `Atom` is index 0 in parser.Kind but index 1 in render.Kind, so the
# two declarations give DIFFERENT answers for the same bare variant --
# the actual hazard. The bare-keyed map holds a single "Kind" entry, so
# the old scan reported exactly one owner and silently emitted the
# survivor's 1 where the real answer was 0 (or vice versa).
lowering.register_enum_variants(make_enum(
    "Kind", "parser.Kind", ["Atom", "List"]))
lowering.register_enum_variants(make_enum(
    "Kind", "render.Kind", ["Table", "Atom", "Grid"]))

expect(lowering.enum_variant_index.has("Kind")).to_equal(true)
expect(lowering.enum_variant_discriminant("parser.Kind", "Atom")).to_equal(0)
expect(lowering.enum_variant_discriminant("render.Kind", "Atom")).to_equal(1)
expect(lowering.variant_owner_keys("Atom").len()).to_equal(2)
```

</details>

#### counts two owners when the bare names differ too

- counts two owners when the bare names differ too
- Verify: counts two owners when the bare names differ too
   - Expected: lowering.variant_owner_keys("Circle").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts two owners when the bare names differ too")
step("Verify: counts two owners when the bare names differ too")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Shape", "geom.Shape", ["Circle", "Square"]))
lowering.register_enum_variants(make_enum(
    "Widget", "ui.Widget", ["Circle", "Slider"]))

# Same discriminant (0 in both) but DIFFERENT enums: a bare
# `case Circle:` cannot be resolved without a qualifier.
expect(lowering.variant_owner_keys("Circle").len()).to_equal(2)
```

</details>

#### still reports a single owner for an uncontested variant

- still reports a single owner for an uncontested variant
- Verify: still reports a single owner for an uncontested variant
   - Expected: lowering.variant_owner_keys("Grid").len() equals `1`
   - Expected: lowering.variant_owner_keys("Grid")[0] equals `render.Kind`
   - Expected: lowering.enum_variant_discriminant("render.Kind", "Grid") equals `2`
   - Expected: lowering.variant_owner_keys("List").len() equals `1`
   - Expected: lowering.enum_variant_discriminant("parser.Kind", "List") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still reports a single owner for an uncontested variant")
step("Verify: still reports a single owner for an uncontested variant")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Kind", "parser.Kind", ["Atom", "List"]))
lowering.register_enum_variants(make_enum(
    "Kind", "render.Kind", ["Table", "Atom", "Grid"]))

# `Grid` is declared only by render.Kind -- index 2 there.
expect(lowering.variant_owner_keys("Grid").len()).to_equal(1)
expect(lowering.variant_owner_keys("Grid")[0]).to_equal("render.Kind")
expect(lowering.enum_variant_discriminant("render.Kind", "Grid")).to_equal(2)
# `List` is declared only by parser.Kind -- index 1 there. This one
# ALSO proves the qualified path reaches an enum the bare map evicted.
expect(lowering.variant_owner_keys("List").len()).to_equal(1)
expect(lowering.enum_variant_discriminant("parser.Kind", "List")).to_equal(1)
```

</details>

#### collapses benign duplicates so ordinary code does not start erroring

- collapses benign duplicates so ordinary code does not start erroring
- Verify: collapses benign duplicates so ordinary code does not start erroring
   - Expected: lowering.enum_variant_index_q.has("ui.a.Colour") is true
   - Expected: lowering.enum_variant_index_q.has("ui.b.Colour") is true
   - Expected: lowering.variant_owner_keys("Blue").len() equals `1`
   - Expected: lowering.enum_variant_discriminant("ui.b.Colour", "Blue") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses benign duplicates so ordinary code does not start erroring")
step("Verify: collapses benign duplicates so ordinary code does not start erroring")
var lowering = MirLowering.new(SymbolTable.new())
# Same bare name, same variants, same discriminants, two modules: the
# 192 identical re-registrations. Counting these as two owners would
# turn every unqualified pattern over them into an ambiguity error.
lowering.register_enum_variants(make_enum(
    "Colour", "ui.a.Colour", ["Red", "Green", "Blue"]))
lowering.register_enum_variants(make_enum(
    "Colour", "ui.b.Colour", ["Red", "Green", "Blue"]))

expect(lowering.enum_variant_index_q.has("ui.a.Colour")).to_equal(true)
expect(lowering.enum_variant_index_q.has("ui.b.Colour")).to_equal(true)
expect(lowering.variant_owner_keys("Blue").len()).to_equal(1)
expect(lowering.enum_variant_discriminant("ui.b.Colour", "Blue")).to_equal(2)
```

</details>

#### reports no owner for a variant nobody declares

- reports no owner for a variant nobody declares
- Verify: reports no owner for a variant nobody declares
   - Expected: lowering.variant_owner_keys("Hexagon").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports no owner for a variant nobody declares")
step("Verify: reports no owner for a variant nobody declares")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Kind", "parser.Kind", ["Atom", "List"]))

expect(lowering.variant_owner_keys("Hexagon").len()).to_equal(0)
```

</details>

### the runtime identity is dual-keyed alongside the variants

#### registers the runtime ID under the runtime_name too

- registers the runtime ID under the runtime_name too
- Verify: registers the runtime ID under the runtime_name too
   - Expected: lowering.enum_runtime_id_index_q.has("web.layout.Style") is true
   - Expected: lowering.enum_runtime_id_index_q.has("term.render.Style") is true
   - Expected: web_id == term_id is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers the runtime ID under the runtime_name too")
step("Verify: registers the runtime ID under the runtime_name too")
var lowering = MirLowering.new(SymbolTable.new())
val web = make_enum("Style", "web.layout.Style", ["Bold", "Italic"])
val term = make_enum("Style", "term.render.Style", ["Plain", "Reverse"])
lowering.register_enum_runtime_id(web)
lowering.register_enum_runtime_id(term)

# The bare map holds one identity; the qualified map holds both, and
# they must DIFFER -- pairing one enum's identity with another's
# discriminant is the same class of silent wrong value.
expect(lowering.enum_runtime_id_index_q.has("web.layout.Style")).to_equal(true)
expect(lowering.enum_runtime_id_index_q.has("term.render.Style")).to_equal(true)
val web_id = lowering.enum_runtime_id_index_q["web.layout.Style"]
val term_id = lowering.enum_runtime_id_index_q["term.render.Style"]
expect(web_id == term_id).to_equal(false)
```

</details>

#### resolves a runtime ID through either key

- resolves a runtime ID through either key
- Verify: resolves a runtime ID through either key


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a runtime ID through either key")
step("Verify: resolves a runtime ID through either key")
var lowering = MirLowering.new(SymbolTable.new())
val web = make_enum("Style", "web.layout.Style", ["Bold", "Italic"])
lowering.register_enum_runtime_id(web)

expect(lowering.enum_runtime_id("web.layout.Style")).to_equal(
    lowering.enum_runtime_id_index["Style"])
```

</details>

### the miss diagnostic names the qualified owner

#### names the EVICTED declaration by its runtime_name

- names the EVICTED declaration by its runtime_name
- Verify: names the EVICTED declaration by its runtime_name


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the EVICTED declaration by its runtime_name")
step("Verify: names the EVICTED declaration by its runtime_name")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

# Before step (c) the scan ran over the bare map, where the evicted
# declaration no longer existed, so it could not be named at all.
val detail = lowering.enum_variant_miss_detail("Style", "Bold")
expect(detail).to_contain("web.layout.Style")
```

</details>

### construction resolves against the constructed enum, not the survivor

#### keeps a construction miss loud when the qualified enum lacks the variant

- keeps a construction miss loud when the qualified enum lacks the variant
- Verify: keeps a construction miss loud when the qualified enum lacks the variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a construction miss loud when the qualified enum lacks the variant")
step("Verify: keeps a construction miss loud when the qualified enum lacks the variant")
var lowering = MirLowering.new(SymbolTable.new())
val web = make_enum("Style", "web.layout.Style", ["Bold", "Italic"])
val term = make_enum("Style", "term.render.Style", ["Plain", "Reverse"])
lowering.register_enum_variants(web)
lowering.register_enum_runtime_id(web)
lowering.register_enum_variants(term)
lowering.register_enum_runtime_id(term)

var builder = lowering.builder
builder.begin_function(SymbolId(id: 7200), "dual_ctor_probe", MirSignature(
    params: [], return_type: MirType.unit(), is_variadic: false), Span.empty())
lowering.builder = builder

val before = lowering.errors.len()
lowering.lower_enum_construct_named("Style", "Bold", [])
expect(lowering.errors.len()).to_be_greater_than(before)
val message = lowering.errors[lowering.errors.len() - 1].message
expect(message).to_contain("enum variant lookup miss")
# Step (c) upgrade: the message now points at the declaration that
# actually owns `Bold`.
expect(message).to_contain("web.layout.Style")
```

</details>

### the other two engines still disagree -- dual-keying is MIR-only

#### interpreter: first-wins drop is still live and observable

- interpreter: first-wins drop is still live and observable
- Verify: interpreter: first-wins drop is still live and observable
   - Expected: enum_table_lookup("Style") equals `Bold,Italic`
   - Expected: enum_table_lookup("Kind") equals `Atom,List,Table,Grid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("interpreter: first-wins drop is still live and observable")
step("Verify: interpreter: first-wins drop is still live and observable")
enum_table_reset()
enum_table_register("Style", ["Bold", "Italic"])
enum_table_register("Style", ["Plain", "Reverse"])

# FIRST-wins -- the exact opposite of MIR's last-wins, on the same
# source. Step (c) does not touch this; step (d) and the registry doc
# own the reconciliation.
expect(enum_table_lookup("Style")).to_equal("Bold,Italic")
# Control that the table is actually live in this process: a fresh
# name must register normally.
enum_table_register("Kind", ["Atom", "List", "Table", "Grid"])
expect(enum_table_lookup("Kind")).to_equal("Atom,List,Table,Grid")
```

</details>

#### rust seed: the discriminant is still derived from the variant name alone

- rust seed: the discriminant is still derived from the variant name alone
- Verify: rust seed: the discriminant is still derived from the variant name alone
   - Expected: seed contains `fn enum_variant_discriminant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rust seed: the discriminant is still derived from the variant name alone")
step("Verify: rust seed: the discriminant is still derived from the variant name alone")
# The seed computes a discriminant by hashing the VARIANT NAME with no
# enum identity at all, so it collapses every bare-name collision by
# construction AND returns a hash rather than the declared ordinal --
# meaning it disagrees numerically with MIR even for enums that do not
# collide. Pinned at the source; reconciling it is step (d).
val seed = read_source(
    "src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs")
# Control that the file was actually read (a missing path would return
# "" and make every `contains` below vacuously false, not true).
expect(seed.contains("fn enum_variant_discriminant")).to_equal(true)
# The signature takes ONLY a variant name -- no enum identity.
expect(seed).to_contain("fn enum_variant_discriminant(variant_name: &str) -> i64")
expect(seed).to_contain("variant_name.hash(&mut hasher)")
expect(seed).to_contain("(hasher.finish() & 0xFFFF_FFFF) as i64")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-MIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `abbd008b84f73061e2e4898f80dc3917487ea89b6b55eecc1d984b937f58bd85`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abbd008b84f73061e2e4898f80dc3917487ea89b6b55eecc1d984b937f58bd85`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abbd008b84f73061e2e4898f80dc3917487ea89b6b55eecc1d984b937f58bd85`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps BOTH sides of a divergent bare-name contest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the EVICTED enum's variant through its runtime_name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT let the bare map rescue a genuine qualified miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
