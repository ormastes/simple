# hir_payload_origin_miss_memo_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hir_payload_origin_miss_memo_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### HIR payload-origin miss memo

#### searches once per (owner, name) for a builtin container spelling

- Verify: searches once per (owner, name) for a builtin container spelling
   - Expected: lowering.payload_origin_miss_skip_count equals `0`
   - Expected: lowering.payload_origin_miss_memo.contains_key("pkg.decl Dict") is true
   - Expected: lowering.payload_origin_miss_skip_count equals `2`
   - Expected: lowering.payload_origin_miss_memo.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: searches once per (owner, name) for a builtin container spelling")
val registry = container_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
val decl = registry.surfaces[0]
val skipped: {text: bool} = {}
# `Dict` alone accounted for 14,847 of the run14 advisories. Three
# importers, one owner, one name: the second and third must cost a
# dict probe, not a search.
lowering.begin_module("pkg/imp1.spl")
lowering.register_materialized_payload_named_dependency(
    decl, "pkg.decl", "Dict", skipped, span)
expect(lowering.payload_origin_miss_skip_count).to_equal(0)
expect(lowering.payload_origin_miss_memo.contains_key("pkg.decl Dict")).to_equal(true)
lowering.begin_module("pkg/imp2.spl")
lowering.register_materialized_payload_named_dependency(
    decl, "pkg.decl", "Dict", skipped, span)
lowering.begin_module("pkg/imp3.spl")
lowering.register_materialized_payload_named_dependency(
    decl, "pkg.decl", "Dict", skipped, span)
# O(1) searches per name: exactly one, plus two memo hits.
expect(lowering.payload_origin_miss_skip_count).to_equal(2)
expect(lowering.payload_origin_miss_memo.len()).to_equal(1)
```

</details>

#### keeps Option and Result distinct, and keys the memo per OWNER

- Verify: keeps Option and Result distinct, and keys the memo per OWNER
   - Expected: lowering.payload_origin_miss_memo.len() equals `3`
   - Expected: lowering.payload_origin_miss_skip_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps Option and Result distinct, and keys the memo per OWNER")
# @req: REQ-SSPEC-LOCAL-001
val registry = container_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
val skipped: {text: bool} = {}
lowering.register_materialized_payload_named_dependency(
    registry.surfaces[0], "pkg.decl", "Option", skipped, span)
lowering.register_materialized_payload_named_dependency(
    registry.surfaces[0], "pkg.decl", "Result", skipped, span)
# A DIFFERENT owner is a different question: two modules may spell the
# same name and only one of them declare it, so a global name-keyed
# memo would be unsound.
lowering.register_materialized_payload_named_dependency(
    registry.surfaces[1], "pkg.imp1", "Option", skipped, span)
expect(lowering.payload_origin_miss_memo.len()).to_equal(3)
expect(lowering.payload_origin_miss_skip_count).to_equal(0)
```

</details>

#### CONTROL: a module that DECLARES `Result` still resolves to its declaration

- Verify: CONTROL: a module that DECLARES `Result` still resolves to its declaration
   - Expected: origin.found is true
   - Expected: origin.item_name equals `Result`
   - Expected: origin.item_kind equals `enum`
   - Expected: lowering.payload_origin_miss_memo.contains_key("pkg.owner Result") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: CONTROL: a module that DECLARES `Result` still resolves to its declaration")
# The correctness half, and the reason the fix is a negative memo
# rather than a capitalized-name filter. `lower_named_kind` puts the
# builtin `Result` arm AFTER the symbol lookup so a declared type wins;
# a name filter would stop materializing this declaration entirely.
val registry = declaring_registry()
var lowering = hirlowering_for_module("pkg/owner.spl", registry)
val owner = registry.surfaces[0]
val origin = lowering.resolve_materialized_enum_payload_origin(
    owner, "pkg.owner", "Result")
expect(origin.found).to_equal(true)
expect(origin.item_name).to_equal("Result")
expect(origin.item_kind).to_equal("enum")
# A HIT is never cached, so no memo entry can ever shadow it.
expect(lowering.payload_origin_miss_memo.contains_key("pkg.owner Result")).to_equal(false)
```

</details>

#### still filters only the lowercase primitives, never the containers

- Verify: still filters only the lowercase primitives, never the containers
   - Expected: hir_dependency_is_builtin_type("text") is true
   - Expected: hir_dependency_is_builtin_type("i64") is true
   - Expected: hir_dependency_is_builtin_type("Dict") is false
   - Expected: hir_dependency_is_builtin_type("Option") is false
   - Expected: hir_dependency_is_builtin_type("Result") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: still filters only the lowercase primitives, never the containers")
# Guards the precedence contract from commit 1aa81cac8c6 against being
# "simplified" into a capitalized-name test.
expect(hir_dependency_is_builtin_type("text")).to_equal(true)
expect(hir_dependency_is_builtin_type("i64")).to_equal(true)
expect(hir_dependency_is_builtin_type("Dict")).to_equal(false)
expect(hir_dependency_is_builtin_type("Option")).to_equal(false)
expect(hir_dependency_is_builtin_type("Result")).to_equal(false)
```

</details>

#### raises no diagnostic and defines no symbol for a memoized miss

- Verify: raises no diagnostic and defines no symbol for a memoized miss
   - Expected: lowering.errors.len() equals `0`
   - Expected: lowering.symbols.lookup_or_invalid("pkg.decl::Dict").is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: raises no diagnostic and defines no symbol for a memoized miss")
# @req: REQ-SSPEC-LOCAL-001
# The cache changes only how the answer is FOUND. A miss bound nothing
# before and binds nothing now, for every importer.
val registry = container_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
val skipped: {text: bool} = {}
lowering.register_materialized_payload_named_dependency(
    registry.surfaces[0], "pkg.decl", "Dict", skipped, span)
lowering.begin_module("pkg/imp2.spl")
lowering.register_materialized_payload_named_dependency(
    registry.surfaces[0], "pkg.decl", "Dict", skipped, span)
expect(lowering.errors.len()).to_equal(0)
expect(lowering.symbols.lookup_or_invalid("pkg.decl::Dict").is_valid()).to_equal(false)
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


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d179ce7108f61852da6f65187620f6ebc05357968ef77f12bcd931f1e40e9d20`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d179ce7108f61852da6f65187620f6ebc05357968ef77f12bcd931f1e40e9d20`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d179ce7108f61852da6f65187620f6ebc05357968ef77f12bcd931f1e40e9d20`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'searches once per (owner, name) for a builtin container spelling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Option and Result distinct, and keys the memo per OWNER' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CONTROL: a module that DECLARES `Result` still resolves to its declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl. -->
