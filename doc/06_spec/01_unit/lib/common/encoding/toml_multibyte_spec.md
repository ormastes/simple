# Toml Multibyte Specification

> Tests covering toml_parse / toml_encode multi-byte.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Toml Multibyte Specification

## Scenarios

### toml_parse / toml_encode multi-byte

#### café/中文/日本語/em-dash/emoji values all parse correctly in one document

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- café/中文/日本語/em-dash/emoji values all parse correctly in one document
   - Expected: entries.len() equals `7`
   - Expected: toml_get(entries, "a") equals `café`
   - Expected: toml_get(entries, "b") equals `中文`
   - Expected: toml_get(entries, "c") equals `日本語`
   - Expected: toml_get(entries, "d") equals `a—b`
   - Expected: toml_get(entries, "e") equals `😀smile`
   - Expected: toml_get(entries, "f") equals `42`
   - Expected: toml_get(entries, "g") equals `tail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("café/中文/日本語/em-dash/emoji values all parse correctly in one document")
val doc = "a = \"café\"\nb = \"中文\"\nc = \"日本語\"\nd = \"a—b\"\ne = \"😀smile\"\nf = 42\ng = \"tail\"\n"
val entries = toml_parse(doc)
expect(entries.len()).to_equal(7)
expect(toml_get(entries, "a")).to_equal("café")
expect(toml_get(entries, "b")).to_equal("中文")
expect(toml_get(entries, "c")).to_equal("日本語")
expect(toml_get(entries, "d")).to_equal("a—b")
expect(toml_get(entries, "e")).to_equal("😀smile")
expect(toml_get(entries, "f")).to_equal("42")
expect(toml_get(entries, "g")).to_equal("tail")
```

</details>

#### round-trips through toml_encode and back

- round-trips through toml_encode and back
   - Expected: roundtrip.len() equals `2`
   - Expected: toml_get(roundtrip, "a") equals `café`
   - Expected: toml_get(roundtrip, "e") equals `😀smile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips through toml_encode and back")
val doc = "a = \"café\"\ne = \"😀smile\"\n"
val entries = toml_parse(doc)
val encoded = toml_encode(entries)
val roundtrip = toml_parse(encoded)
expect(roundtrip.len()).to_equal(2)
expect(toml_get(roundtrip, "a")).to_equal("café")
expect(toml_get(roundtrip, "e")).to_equal("😀smile")
```

</details>

#### pure ASCII is unaffected (regression guard)

- pure ASCII is unaffected (regression guard)
   - Expected: entries.len() equals `2`
   - Expected: toml_get(entries, "name") equals `ascii`
   - Expected: toml_get(entries, "other") equals `plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pure ASCII is unaffected (regression guard)")
val doc = "name = \"ascii\"\nother = \"plain\"\n"
val entries = toml_parse(doc)
expect(entries.len()).to_equal(2)
expect(toml_get(entries, "name")).to_equal("ascii")
expect(toml_get(entries, "other")).to_equal("plain")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/toml_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering toml_parse / toml_encode multi-byte.
- toml_parse / toml_encode multi-byte

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `7aa52b641826e6c36b146c947011e8211cbca6b751e23862b978029f8d40f0ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7aa52b641826e6c36b146c947011e8211cbca6b751e23862b978029f8d40f0ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7aa52b641826e6c36b146c947011e8211cbca6b751e23862b978029f8d40f0ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/encoding/toml_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/toml_multibyte_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/toml_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/toml_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/toml_multibyte_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/encoding/toml_multibyte_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'café/中文/日本語/em-dash/emoji values all parse correctly in one document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/toml_multibyte_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips through toml_encode and back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/toml_multibyte_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pure ASCII is unaffected (regression guard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
