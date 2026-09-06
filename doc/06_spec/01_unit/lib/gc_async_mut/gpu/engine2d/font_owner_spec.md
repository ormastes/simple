# font_owner_spec

> Engine2D canonical font-renderer ownership and lifecycle coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# font_owner_spec

Engine2D canonical font-renderer ownership and lifecycle coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine2D canonical font-renderer ownership and lifecycle coverage.

## Scenarios

### Engine2D font owner lifecycle

#### starts empty and creates one canonical renderer lazily

- starts empty and creates one canonical renderer lazily
   - Expected: owner.active.len() equals `1`
   - Expected: owner.active.len() equals `1`
   - Expected: first.ttf_handle equals `second.ttf_handle`
   - Expected: first.atlas_generation equals `second.atlas_generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts empty and creates one canonical renderer lazily")
var owner = Engine2DFontOwner.new()
expect_not(engine2d_font_owner_has(owner))
val first = engine2d_font_owner_get_or_create(owner)
assert_true(engine2d_font_owner_has(owner))
expect(owner.active.len()).to_equal(1)
val second = engine2d_font_owner_get_or_create(owner)
expect(owner.active.len()).to_equal(1)
expect(first.ttf_handle).to_equal(second.ttf_handle)
expect(first.atlas_generation).to_equal(second.atlas_generation)
```

</details>

#### stores an explicit renderer and clears both populated and empty owners

- stores an explicit renderer and clears both populated and empty owners
   - Expected: owner.active.len() equals `1`
   - Expected: owner.active.len() equals `0`
   - Expected: owner.active.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores an explicit renderer and clears both populated and empty owners")
var owner = Engine2DFontOwner.new()
val renderer = FontRenderer.bitmap_only()
owner = engine2d_font_owner_store(owner, renderer)
assert_true(engine2d_font_owner_has(owner))
expect(owner.active.len()).to_equal(1)
owner = engine2d_font_owner_clear(owner)
expect_not(engine2d_font_owner_has(owner))
expect(owner.active.len()).to_equal(0)
owner = engine2d_font_owner_clear(owner)
expect(owner.active.len()).to_equal(0)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `47d5dc0b28b86206c99fc273cf6755fd9e8ede550b29ea0584ffb56b6674a976`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47d5dc0b28b86206c99fc273cf6755fd9e8ede550b29ea0584ffb56b6674a976`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47d5dc0b28b86206c99fc273cf6755fd9e8ede550b29ea0584ffb56b6674a976`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts empty and creates one canonical renderer lazily' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/font_owner_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores an explicit renderer and clears both populated and empty owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
