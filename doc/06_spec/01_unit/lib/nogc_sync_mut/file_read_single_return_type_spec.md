# File Read Single Return Type Specification

> Tests covering file_read has a single return type, app.io.mod re-exports both byte-read shapes.

### No definition of file_read returns an optional

1. List files defining `file_read` with an optional return; expect an empty list.
2. Count them; expect zero.

# File Read Single Return Type Specification

## Scenarios

### file_read has a single return type

#### positive control: the scanner finds a definition that certainly exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- positive control: the scanner finds a definition that certainly exists
   - Expected: definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(") >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("positive control: the scanner finds a definition that certainly exists")
# `file_read_opt` is introduced by the same change this spec guards.
expect(definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(") >= 1).to_equal(true)
```

</details>

#### negative control: the scanner does not match a symbol that cannot exist

- negative control: the scanner does not match a symbol that cannot exist
   - Expected: definition_count("^[[:space:]]*(pub )?fn file_read_no_such_symbol_xyzzy\\(") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("negative control: the scanner does not match a symbol that cannot exist")
expect(definition_count("^[[:space:]]*(pub )?fn file_read_no_such_symbol_xyzzy\\(")).to_equal(0)
```

</details>

#### no definition of file_read returns an optional

- no definition of file_read returns an optional
   - Expected: owners equals ``
   - Expected: definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text\\?:") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("no definition of file_read returns an optional")
# This is the property that was fixed. `-> text?` and `-> text` are not
# substitutable: the optional form carries an absence case the plain
# form does not.
val owners = definition_owners("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text\\?:")
# Surfacing the owner list makes a failure self-diagnosing: it names the
# file that reintroduced the optional shape.
expect(owners).to_equal("")
expect(definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text\\?:")).to_equal(0)
```

</details>

#### every definition of file_read shares the plain text return type

- every definition of file_read shares the plain text return type
   - Expected: total >= 1 is true
   - Expected: plain equals `total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("every definition of file_read shares the plain text return type")
# Total count and plain-text count must agree: any definition with some
# third return type would make these diverge.
val total = definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\)")
val plain = definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text:")
expect(total >= 1).to_equal(true)
expect(plain).to_equal(total)
```

</details>

#### the optional-returning reads live under their own name

- the optional-returning reads live under their own name
   - Expected: opt_typed equals `opt_total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the optional-returning reads live under their own name")
# All three relocated definitions must still return the optional shape;
# if one silently became `-> text` the absence path was dropped rather
# than renamed.
val opt_total = definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(path: text\\)")
val opt_typed = definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(path: text\\) -> text\\?:")
expect(opt_typed).to_equal(opt_total)
```

</details>

#### the canonical text read is still exported exactly once

- the canonical text read is still exported exactly once
   - Expected: definition_count("^[[:space:]]*pub fn file_read\\(path: text\\)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the canonical text read is still exported exactly once")
# `io_runtime.spl` holds the single `pub` definition; the others are
# module-local. A second `pub` would reintroduce cross-module ambiguity.
expect(definition_count("^[[:space:]]*pub fn file_read\\(path: text\\)")).to_equal(1)
```

</details>

### app.io.mod re-exports both byte-read shapes

#### negative control: the scanner does not match an absent symbol

- negative control: the scanner does not match an absent symbol
   - Expected: shim_exports("file_read_bytes_no_such_symbol_xyzzy") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("negative control: the scanner does not match an absent symbol")
expect(shim_exports("file_read_bytes_no_such_symbol_xyzzy")).to_equal(0)
```

</details>

#### re-exports the canonical [u8] byte read

- re-exports the canonical [u8] byte read
   - Expected: shim_exports("file_read_bytes") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports the canonical [u8] byte read")
expect(shim_exports("file_read_bytes")).to_equal(2)
```

</details>

#### re-exports the raw [i64] byte read

- re-exports the raw [i64] byte read
   - Expected: shim_exports("file_read_bytes_i64") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports the raw [i64] byte read")
expect(shim_exports("file_read_bytes_i64")).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering file_read has a single return type, app.io.mod re-exports both byte-read shapes.
- file_read has a single return type
- app.io.mod re-exports both byte-read shapes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-IOREAD-007`
- `REQ-IOREAD-008`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9416c508852877d52b27bdd16d11042c05b8a8fa8b61764d5287110da969c2f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9416c508852877d52b27bdd16d11042c05b8a8fa8b61764d5287110da969c2f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9416c508852877d52b27bdd16d11042c05b8a8fa8b61764d5287110da969c2f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: the scanner finds a definition that certainly exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negative control: the scanner does not match a symbol that cannot exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no definition of file_read returns an optional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
