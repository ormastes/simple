# Treesitter Visibility Specification

> Tests covering TreeSitter Scoped Visibility Parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Visibility Specification

## Scenarios

### TreeSitter Scoped Visibility Parsing

#### parses scoped visibility on top-level declarations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses scoped visibility on top-level declarations
   - Expected: outline.functions.len() equals `2`
   - Expected: outline.functions[0].visibility equals `Visibility.Peer`
   - Expected: outline.functions[0].is_public is false
   - Expected: outline.enums[0].visibility equals `Visibility.Up`
   - Expected: outline.constants[0].visibility equals `Visibility.Internal`
   - Expected: outline.constants[1].visibility equals `Visibility.Package`
   - Expected: outline.functions[1].visibility equals `Visibility.Private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses scoped visibility on top-level declarations")
val src = "pub(peer) fn peer_fn():\n    pass_dn\n\npub(up) enum ParentOnly:\n    Ready\n\npub(friend) val internal_value: i64 = 1\npub(package) val package_value: i64 = 2\npri fn local_fn():\n    pass_dn\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()

expect(outline.functions.len()).to_equal(2)
expect(outline.functions[0].visibility).to_equal(Visibility.Peer)
expect(outline.functions[0].is_public).to_equal(false)
expect(outline.enums[0].visibility).to_equal(Visibility.Up)
expect(outline.constants[0].visibility).to_equal(Visibility.Internal)
expect(outline.constants[1].visibility).to_equal(Visibility.Package)
expect(outline.functions[1].visibility).to_equal(Visibility.Private)
```

</details>

#### parses scoped visibility on class and impl members

- parses scoped visibility on class and impl members
   - Expected: outline.classes.len() equals `1`
   - Expected: outline.classes[0].methods.len() equals `1`
   - Expected: outline.classes[0].methods[0].visibility equals `Visibility.Peer`
   - Expected: outline.classes[0].fields[0].visibility equals `Visibility.Up`
   - Expected: outline.impls.len() equals `1`
   - Expected: outline.impls[0].methods.len() equals `1`
   - Expected: outline.impls[0].methods[0].visibility equals `Visibility.Package`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses scoped visibility on class and impl members")
val src = "class Widget:\n    pub(peer) fn peer_method():\n        pass_dn\n    pub(up) helper: i64\n\nimpl Widget:\n    pub(package) fn package_method():\n        pass_dn\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()

expect(outline.classes.len()).to_equal(1)
expect(outline.classes[0].methods.len()).to_equal(1)
expect(outline.classes[0].methods[0].visibility).to_equal(Visibility.Peer)
expect(outline.classes[0].fields[0].visibility).to_equal(Visibility.Up)
expect(outline.impls.len()).to_equal(1)
expect(outline.impls[0].methods.len()).to_equal(1)
expect(outline.impls[0].methods[0].visibility).to_equal(Visibility.Package)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/treesitter_visibility_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TreeSitter Scoped Visibility Parsing.
- TreeSitter Scoped Visibility Parsing

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

- Canonical SPipe generation for source `541279d438fa616da2ed4fab172e0b5c5354062438c77a8b863e5b4e7cab1a77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `541279d438fa616da2ed4fab172e0b5c5354062438c77a8b863e5b4e7cab1a77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `541279d438fa616da2ed4fab172e0b5c5354062438c77a8b863e5b4e7cab1a77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/parser/treesitter_visibility_spec.spl
mirror: doc/06_spec/unit/compiler/parser/treesitter_visibility_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/treesitter_visibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/treesitter_visibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/treesitter_visibility_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/treesitter_visibility_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses scoped visibility on top-level declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_visibility_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses scoped visibility on class and impl members' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
