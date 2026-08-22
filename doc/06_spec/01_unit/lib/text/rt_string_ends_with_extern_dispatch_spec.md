# rt_string_ends_with_extern_dispatch_spec

> Category: Stdlib

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rt_string_ends_with_extern_dispatch_spec

Category: Stdlib

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

Category: Stdlib
Status: Active

## Scenarios

### rt_string_ends_with extern is dispatchable

#### matches a present suffix

- Verify: matches a present suffix
   - Expected: rt_string_ends_with("notes.md", ".md") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: matches a present suffix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_ends_with("notes.md", ".md")).to_equal(true)
```

</details>

#### rejects a near-miss suffix

- Verify: rejects a near-miss suffix
   - Expected: rt_string_ends_with("notes.mdx", ".md") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: rejects a near-miss suffix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_ends_with("notes.mdx", ".md")).to_equal(false)
```

</details>

#### rejects a suffix longer than the subject

- Verify: rejects a suffix longer than the subject
   - Expected: rt_string_ends_with("md", ".md") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: rejects a suffix longer than the subject")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_ends_with("md", ".md")).to_equal(false)
```

</details>

#### treats the whole subject as its own suffix

- Verify: treats the whole subject as its own suffix
   - Expected: rt_string_ends_with(".md", ".md") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: treats the whole subject as its own suffix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_ends_with(".md", ".md")).to_equal(true)
```

</details>

#### accepts the empty suffix

- Verify: accepts the empty suffix
   - Expected: rt_string_ends_with("anything", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: accepts the empty suffix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_ends_with("anything", "")).to_equal(true)
```

</details>

#### finds no suffix in the empty subject

- Verify: finds no suffix in the empty subject
   - Expected: rt_string_ends_with("", ".md") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: finds no suffix in the empty subject")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_ends_with("", ".md")).to_equal(false)
```

</details>

### rt_string_rfind extern is dispatchable

#### returns the LAST byte index, not the first

- Verify: returns the LAST byte index, not the first
   - Expected: rt_string_rfind("a/b/c", "/") equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: returns the LAST byte index, not the first")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_rfind("a/b/c", "/")).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns the last of overlapping-free repeats

- Verify: returns the last of overlapping-free repeats
   - Expected: rt_string_rfind("abcabc", "abc") equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: returns the last of overlapping-free repeats")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_rfind("abcabc", "abc")).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns 0 when the needle is the whole subject

- Verify: returns 0 when the needle is the whole subject
   - Expected: rt_string_rfind("abc", "abc") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: returns 0 when the needle is the whole subject")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_rfind("abc", "abc")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 on a miss

- Verify: returns -1 on a miss
   - Expected: rt_string_rfind("abc", "zz") equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: returns -1 on a miss")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_rfind("abc", "zz")).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when the needle is longer than the subject

- Verify: returns -1 when the needle is longer than the subject
   - Expected: rt_string_rfind("ab", "abc") equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: returns -1 when the needle is longer than the subject")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_rfind("ab", "abc")).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns the subject length for an empty needle

- Verify: returns the subject length for an empty needle
   - Expected: rt_string_rfind("abc", "") equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TEXT_RT_STRING_ENDS_WITH_EXT-001
step("Verify: returns the subject length for an empty needle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(rt_string_rfind("abc", "")).to_equal(3)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c120ebb49eb052a4998dd24657930db7663a6c0c179998d38da876bd796cc8cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c120ebb49eb052a4998dd24657930db7663a6c0c179998d38da876bd796cc8cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c120ebb49eb052a4998dd24657930db7663a6c0c179998d38da876bd796cc8cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
