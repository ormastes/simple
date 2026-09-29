# Domain Block HIR Lowering Unit Spec

> Verifies that top-level domain blocks survive the pure Simple frontend and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Domain Block HIR Lowering Unit Spec

Verifies that top-level domain blocks survive the pure Simple frontend and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/domain_block_hir_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that top-level domain blocks survive the pure Simple frontend and
arrive in HIR metadata without stealing ordinary identifier usage.

## Scenarios

### domain block HIR lowering

#### captures schema and style blocks at module scope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures schema and style blocks at module scope
   - Expected: module.domain_blocks.len() equals `2`
   - Expected: module.domain_blocks[0].kind equals `schema`
   - Expected: module.domain_blocks[0].payload equals `Building: id Uuid`
   - Expected: module.domain_blocks[0].context equals `module`
   - Expected: module.domain_blocks[1].kind equals `style`
   - Expected: module.domain_blocks[1].payload equals `Button.primary: padding 8px`
   - Expected: hir.domain_blocks.len() equals `2`
   - Expected: hir.domain_blocks[0].kind equals `schema`
   - Expected: hir.domain_blocks[0].payload equals `Building: id Uuid`
   - Expected: hir.domain_blocks[1].kind equals `style`
   - Expected: hir.domain_blocks[1].payload equals `Button.primary: padding 8px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures schema and style blocks at module scope")
val log = make_logger()
val source = "schema{Building: id Uuid}\nstyle{Button.primary: padding 8px}"
val module = parse_full_frontend(source, "domain_blocks", "domain_blocks", log)

expect(module.domain_blocks.len()).to_equal(2)
expect(module.domain_blocks[0].kind).to_equal("schema")
expect(module.domain_blocks[0].payload).to_equal("Building: id Uuid")
expect(module.domain_blocks[0].context).to_equal("module")
expect(module.domain_blocks[1].kind).to_equal("style")
expect(module.domain_blocks[1].payload).to_equal("Button.primary: padding 8px")

val hir = HirLowering.with_filename("domain_blocks").lower_module(module)
expect(hir.domain_blocks.len()).to_equal(2)
expect(hir.domain_blocks[0].kind).to_equal("schema")
expect(hir.domain_blocks[0].payload).to_equal("Building: id Uuid")
expect(hir.domain_blocks[1].kind).to_equal("style")
expect(hir.domain_blocks[1].payload).to_equal("Button.primary: padding 8px")
```

</details>

#### does not treat ordinary schema identifiers as domain blocks

- does not treat ordinary schema identifiers as domain blocks
   - Expected: module.domain_blocks.len() equals `0`
   - Expected: module.constants.has("schema") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat ordinary schema identifiers as domain blocks")
val log = make_logger()
val source = "val schema = 1"
val module = parse_full_frontend(source, "schema_ident", "schema_ident", log)

expect(module.domain_blocks.len()).to_equal(0)
expect(module.constants.has("schema")).to_equal(true)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f8a2a097f951dc11e7e9392f242ad0bfd0658338a9ad86a59dd796a25f69fb1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f8a2a097f951dc11e7e9392f242ad0bfd0658338a9ad86a59dd796a25f69fb1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f8a2a097f951dc11e7e9392f242ad0bfd0658338a9ad86a59dd796a25f69fb1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/hir/domain_block_hir_lowering_spec.spl
mirror: doc/06_spec/unit/compiler/hir/domain_block_hir_lowering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/domain_block_hir_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/domain_block_hir_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/domain_block_hir_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/hir/domain_block_hir_lowering_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures schema and style blocks at module scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/domain_block_hir_lowering_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat ordinary schema identifiers as domain blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
