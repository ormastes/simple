# rt_string_ends_with_extern_dispatch_spec

> Feature: Text Extern Dispatch Parity

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rt_string_ends_with_extern_dispatch_spec

Feature: Text Extern Dispatch Parity

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Text Extern Dispatch Parity
Category: Stdlib
Status: Active

## Scenarios

### rt_string_ends_with extern is dispatchable

#### matches a present suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### rejects a near-miss suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_ends_with("notes.mdx", ".md")).to_equal(false)
```

</details>

#### rejects a suffix longer than the subject

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_ends_with("md", ".md")).to_equal(false)
```

</details>

#### treats the whole subject as its own suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_ends_with(".md", ".md")).to_equal(true)
```

</details>

#### accepts the empty suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_ends_with("anything", "")).to_equal(true)
```

</details>

#### finds no suffix in the empty subject

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_ends_with("", ".md")).to_equal(false)
```

</details>

### rt_string_rfind extern is dispatchable

#### returns the LAST byte index, not the first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_rfind("a/b/c", "/")).to_equal(3)
```

</details>

#### returns the last of overlapping-free repeats

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_rfind("abcabc", "abc")).to_equal(3)
```

</details>

#### returns 0 when the needle is the whole subject

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_rfind("abc", "abc")).to_equal(0)
```

</details>

#### returns -1 on a miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_rfind("abc", "zz")).to_equal(-1)
```

</details>

#### returns -1 when the needle is longer than the subject

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_rfind("ab", "abc")).to_equal(-1)
```

</details>

#### returns the subject length for an empty needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_string_rfind("abc", "")).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `e57d26d91ee7d50a33e815c4977f4b6028efae0ce6493ec53873386425958dec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e57d26d91ee7d50a33e815c4977f4b6028efae0ce6493ec53873386425958dec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e57d26d91ee7d50a33e815c4977f4b6028efae0ce6493ec53873386425958dec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl:59:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches a present suffix' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects a near-miss suffix' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl:67:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects a suffix longer than the subject' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'treats the whole subject as its own suffix' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
