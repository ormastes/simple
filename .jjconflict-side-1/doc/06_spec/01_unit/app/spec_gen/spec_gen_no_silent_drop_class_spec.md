# spec_gen_no_silent_drop_class_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_gen_no_silent_drop_class_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### positive control - the generator really produces content

#### emits headings and bullets for a known-good spec source

- Verify: emits headings and bullets for a known-good spec source
   - Expected: doc contains `## control suite`
   - Expected: doc contains `- control case one`
   - Expected: doc contains `- control case two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: emits headings and bullets for a known-good spec source")
# @req: REQ-SSPEC-LOCAL-001
val src = "describe \"control suite\":\n    it \"control case one\":\n        pass\n    it(\"control case two\"):\n        pass\n"
val doc = extract_spec_doc(src, "control_spec.spl")
expect(doc.contains("## control suite")).to_equal(true)
expect(doc.contains("- control case one")).to_equal(true)
expect(doc.contains("- control case two")).to_equal(true)
```

</details>

#### emits a non-root mirror directory for a real test path

- Verify: emits a non-root mirror directory for a real test path
   - Expected: rel == "" is false
   - Expected: rel equals `01_unit/app/spec_gen`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: emits a non-root mirror directory for a real test path")
val rel = spec_relative_dir("test/01_unit/app/spec_gen/x_spec.spl")
expect(rel == "").to_equal(false)
expect(rel).to_equal("01_unit/app/spec_gen")
```

</details>

### no spec file in a scoped sweep is dropped silently

#### extracts content from every *_spec.spl under test/01_unit/app/office

- Verify: extracts content from every *_spec.spl under test/01_unit/app/office
   - Expected: considered > 0 is true
   - Expected: empty.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: extracts content from every *_spec.spl under test/01_unit/app/office")
# @req: REQ-SSPEC-LOCAL-001
val files = dir_walk("test/01_unit/app/office")
var considered = 0
var empty: [text] = []
for f in files:
    if not f.ends_with("_spec.spl"):
        continue
    considered = considered + 1
    if extract_spec_doc(file_read(f), f).trim() == "":
        empty.push(f)
# The sweep itself must not be vacuous - zero files considered would
# make the "nothing dropped" assertion below meaningless.
expect(considered > 0).to_equal(true)
expect(empty.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38e1cd9a1f924e98dbc99e676a785596ca9383c98c99c19777475752ea86d031`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38e1cd9a1f924e98dbc99e676a785596ca9383c98c99c19777475752ea86d031`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38e1cd9a1f924e98dbc99e676a785596ca9383c98c99c19777475752ea86d031`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl
mirror: doc/06_spec/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits headings and bullets for a known-good spec source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a non-root mirror directory for a real test path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts content from every *_spec.spl under test/01_unit/app/office' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/app/spec_gen/spec_gen_no_silent_drop_class_spec.spl. -->
