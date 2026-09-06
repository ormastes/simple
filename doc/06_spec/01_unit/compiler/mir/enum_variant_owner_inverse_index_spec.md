# enum_variant_owner_inverse_index_spec

> Purpose: Prove that the enum variant-owner inverse index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# enum_variant_owner_inverse_index_spec

Purpose: Prove that the enum variant-owner inverse index.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that the enum variant-owner inverse index.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### the enum variant-owner inverse index

#### names the unique owner of a variant leaf without scanning the keyspace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names the unique owner of a variant leaf without scanning the keyspace
- Verify: names the unique owner of a variant leaf without scanning the keyspace
   - Expected: lowering.enum_variant_owners["CodegenError"].len() equals `1`
   - Expected: lowering.enum_variant_owners["CodegenError"][0] equals `CompileResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the unique owner of a variant leaf without scanning the keyspace")
step("Verify: names the unique owner of a variant leaf without scanning the keyspace")
# @req: REQ-COMPILER-MIR-001
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "CompileResult", "driver.CompileResult", ["Success", "CodegenError"]))

# This is the exact recovery the stalling call site performs for
# `CompileResult.CodegenError(..)`, now as one dict lookup.
expect(lowering.enum_variant_owners.has("CodegenError")).to_be_true()
expect(lowering.enum_variant_owners["CodegenError"].len()).to_equal(1)
expect(lowering.enum_variant_owners["CodegenError"][0]).to_equal("CompileResult")
```

</details>

#### refuses recovery when two distinct enums declare the same variant leaf

- refuses recovery when two distinct enums declare the same variant leaf
- Verify: refuses recovery when two distinct enums declare the same variant leaf
   - Expected: lowering.enum_variant_owners["CodegenError"].len() equals `2`
   - Expected: lowering.enum_variant_owners["Skipped"].len() equals `1`
   - Expected: lowering.enum_variant_owners["Skipped"][0] equals `EmitResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("refuses recovery when two distinct enums declare the same variant leaf")
step("Verify: refuses recovery when two distinct enums declare the same variant leaf")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "CompileResult", "driver.CompileResult", ["Success", "CodegenError"]))
lowering.register_enum_variants(make_enum(
    "EmitResult", "backend.EmitResult", ["CodegenError", "Skipped"]))

# Two owners, so the list is not a singleton and the conservative
# fallback declines -- exactly what the old `count == 1` scan did.
expect(lowering.enum_variant_owners["CodegenError"].len()).to_equal(2)
# A leaf that is still unique stays recoverable.
expect(lowering.enum_variant_owners["Skipped"].len()).to_equal(1)
expect(lowering.enum_variant_owners["Skipped"][0]).to_equal("EmitResult")
```

</details>

#### withdraws the leaves an evicted bare-name registration no longer owns

- withdraws the leaves an evicted bare-name registration no longer owns
- Verify: withdraws the leaves an evicted bare-name registration no longer owns
   - Expected: lowering.enum_variant_owners["Italic"].len() equals `0`
   - Expected: lowering.enum_variant_owners["Reverse"].len() equals `1`
   - Expected: lowering.enum_variant_owners["Reverse"][0] equals `Style`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("withdraws the leaves an evicted bare-name registration no longer owns")
step("Verify: withdraws the leaves an evicted bare-name registration no longer owns")
var lowering = MirLowering.new(SymbolTable.new())
# `enum_variant_index` is keyed by the BARE name and is last-wins, so
# the second registration EVICTS the first. Without withdrawal,
# "Italic" would keep naming an owner that no longer declares it.
lowering.register_enum_variants(make_enum(
    "Style", "web.layout.Style", ["Bold", "Italic"]))
lowering.register_enum_variants(make_enum(
    "Style", "term.render.Style", ["Plain", "Reverse"]))

expect(lowering.enum_variant_owners.has("Italic")).to_be_true()
expect(lowering.enum_variant_owners["Italic"].len()).to_equal(0)
expect(lowering.enum_variant_owners["Reverse"].len()).to_equal(1)
expect(lowering.enum_variant_owners["Reverse"][0]).to_equal("Style")
```

</details>

#### does not double-list an owner that re-registers the identical set

- does not double-list an owner that re-registers the identical set
- Verify: does not double-list an owner that re-registers the identical set
   - Expected: lowering.enum_variant_owners["CodegenError"].len() equals `1`
   - Expected: lowering.enum_variant_owners["CodegenError"][0] equals `CompileResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not double-list an owner that re-registers the identical set")
step("Verify: does not double-list an owner that re-registers the identical set")
var lowering = MirLowering.new(SymbolTable.new())
lowering.register_enum_variants(make_enum(
    "CompileResult", "driver.CompileResult", ["Success", "CodegenError"]))
lowering.register_enum_variants(make_enum(
    "CompileResult", "driver.CompileResult", ["Success", "CodegenError"]))

# A benign identical re-registration must stay a UNIQUE owner; if it
# accumulated, the fallback would stop recovering real constructions.
expect(lowering.enum_variant_owners["CodegenError"].len()).to_equal(1)
expect(lowering.enum_variant_owners["CodegenError"][0]).to_equal("CompileResult")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `82dfd4071a4c16b794fbbd2f78a61625ee68d3e4ded9d2025cd8354ddb2d193e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82dfd4071a4c16b794fbbd2f78a61625ee68d3e4ded9d2025cd8354ddb2d193e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82dfd4071a4c16b794fbbd2f78a61625ee68d3e4ded9d2025cd8354ddb2d193e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the unique owner of a variant leaf without scanning the keyspace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses recovery when two distinct enums declare the same variant leaf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'withdraws the leaves an evicted bare-name registration no longer owns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
