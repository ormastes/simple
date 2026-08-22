# file_read_single_return_type_spec

> Verifies the file read single return type behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# file_read_single_return_type_spec

Verifies the file read single return type behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the file read single return type behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### file_read has a single return type

#### positive control: the scanner finds a definition that certainly exists

- Verify: positive control: the scanner finds a definition that certainly exists
   - Expected: definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(") >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: positive control: the scanner finds a definition that certainly exists")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# `file_read_opt` is introduced by the same change this spec guards.
expect(definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(") >= 1).to_equal(true)
```

</details>

#### negative control: the scanner does not match a symbol that cannot exist

- Verify: negative control: the scanner does not match a symbol that cannot exist
   - Expected: definition_count("^[[:space:]]*(pub )?fn file_read_no_such_symbol_xyzzy\\(") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: negative control: the scanner does not match a symbol that cannot exist")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(definition_count("^[[:space:]]*(pub )?fn file_read_no_such_symbol_xyzzy\\(")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### no definition of file_read returns an optional

- Verify: no definition of file_read returns an optional
   - Expected: owners equals ``
   - Expected: definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text\\?:") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: no definition of file_read returns an optional")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# This is the property that was fixed. `-> text?` and `-> text` are not
# substitutable: the optional form carries an absence case the plain
# form does not.
val owners = definition_owners("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text\\?:")
# Surfacing the owner list makes a failure self-diagnosing: it names the
# file that reintroduced the optional shape.
expect(owners).to_equal("")
expect(definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text\\?:")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### every definition of file_read shares the plain text return type

- Verify: every definition of file_read shares the plain text return type
   - Expected: total >= 1 is true
   - Expected: plain equals `total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: every definition of file_read shares the plain text return type")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Total count and plain-text count must agree: any definition with some
# third return type would make these diverge.
val total = definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\)")
val plain = definition_count("^[[:space:]]*(pub )?fn file_read\\(path: text\\) -> text:")
expect(total >= 1).to_equal(true)
expect(plain).to_equal(total)
```

</details>

#### the optional-returning reads live under their own name

- Verify: the optional-returning reads live under their own name
   - Expected: opt_typed equals `opt_total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: the optional-returning reads live under their own name")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# All three relocated definitions must still return the optional shape;
# if one silently became `-> text` the absence path was dropped rather
# than renamed.
val opt_total = definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(path: text\\)")
val opt_typed = definition_count("^[[:space:]]*(pub )?fn file_read_opt\\(path: text\\) -> text\\?:")
expect(opt_typed).to_equal(opt_total)
```

</details>

#### the canonical text read is still exported exactly once

- Verify: the canonical text read is still exported exactly once
   - Expected: definition_count("^[[:space:]]*pub fn file_read\\(path: text\\)") equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: the canonical text read is still exported exactly once")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# `io_runtime.spl` holds the single `pub` definition; the others are
# module-local. A second `pub` would reintroduce cross-module ambiguity.
expect(definition_count("^[[:space:]]*pub fn file_read\\(path: text\\)")).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

### app.io.mod re-exports both byte-read shapes

#### negative control: the scanner does not match an absent symbol

- Verify: negative control: the scanner does not match an absent symbol
   - Expected: shim_exports("file_read_bytes_no_such_symbol_xyzzy") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: negative control: the scanner does not match an absent symbol")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(shim_exports("file_read_bytes_no_such_symbol_xyzzy")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### re-exports the canonical [u8] byte read

- Verify: re-exports the canonical [u8] byte read
   - Expected: shim_exports("file_read_bytes") equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: re-exports the canonical [u8] byte read")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(shim_exports("file_read_bytes")).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### re-exports the raw [i64] byte read

- Verify: re-exports the raw [i64] byte read
   - Expected: shim_exports("file_read_bytes_i64") equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-IOREAD-007 REQ-IOREAD-008
step("Verify: re-exports the raw [i64] byte read")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(shim_exports("file_read_bytes_i64")).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `13bb8ba8eff6c9e0707a75122882cd7e5143c859e4aea2df7606a7a468c9ec3b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13bb8ba8eff6c9e0707a75122882cd7e5143c859e4aea2df7606a7a468c9ec3b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13bb8ba8eff6c9e0707a75122882cd7e5143c859e4aea2df7606a7a468c9ec3b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
