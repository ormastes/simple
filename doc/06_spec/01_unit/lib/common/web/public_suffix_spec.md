# Public Suffix Specification

> Tests covering Public Suffix List.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Public Suffix Specification

## Scenarios

### Public Suffix List

#### matches exact private wildcard exception and IDNA rules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches exact private wildcard exception and IDNA rules
   - Expected: is_public_suffix("com") is true
   - Expected: is_public_suffix("co.uk") is true
   - Expected: is_public_suffix("github.io") is true
   - Expected: is_public_suffix("foo.ck") is true
   - Expected: is_public_suffix("www.ck") is false
   - Expected: is_public_suffix("foo.kawasaki.jp") is true
   - Expected: is_public_suffix("city.kawasaki.jp") is false
   - Expected: is_public_suffix("公司.cn") is true
   - Expected: is_public_suffix("xn--55qx5d.cn") is true
   - Expected: is_public_suffix("example.com") is false
   - Expected: is_public_suffix("internal") is true
   - Expected: PUBLIC_SUFFIX_SOURCE_COMMIT.len() equals `40`
   - Expected: PUBLIC_SUFFIX_SOURCE_SHA256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches exact private wildcard exception and IDNA rules")
expect(is_public_suffix("com")).to_equal(true)
expect(is_public_suffix("co.uk")).to_equal(true)
expect(is_public_suffix("github.io")).to_equal(true)
expect(is_public_suffix("foo.ck")).to_equal(true)
expect(is_public_suffix("www.ck")).to_equal(false)
expect(is_public_suffix("foo.kawasaki.jp")).to_equal(true)
expect(is_public_suffix("city.kawasaki.jp")).to_equal(false)
expect(is_public_suffix("公司.cn")).to_equal(true)
expect(is_public_suffix("xn--55qx5d.cn")).to_equal(true)
expect(is_public_suffix("example.com")).to_equal(false)
expect(is_public_suffix("internal")).to_equal(true)
expect(PUBLIC_SUFFIX_SOURCE_COMMIT.len()).to_equal(40)
expect(PUBLIC_SUFFIX_SOURCE_SHA256.len()).to_equal(64)
```

</details>

#### returns the registrable domain and rejects unusable hosts

- returns the registrable domain and rejects unusable hosts
   - Expected: registrable_domain("www.shop.example.com") equals `example.com`
   - Expected: registrable_domain("a.b.example.co.uk") equals `example.co.uk`
   - Expected: registrable_domain("a.foo.kawasaki.jp") equals `a.foo.kawasaki.jp`
   - Expected: registrable_domain("city.kawasaki.jp") equals `city.kawasaki.jp`
   - Expected: registrable_domain("www.city.kawasaki.jp") equals `city.kawasaki.jp`
   - Expected: registrable_domain("www.ck") equals `www.ck`
   - Expected: registrable_domain("com") equals ``
   - Expected: registrable_domain("bad..example.com") equals ``
   - Expected: registrable_domain("-bad.example.com") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the registrable domain and rejects unusable hosts")
expect(registrable_domain("www.shop.example.com")).to_equal("example.com")
expect(registrable_domain("a.b.example.co.uk")).to_equal("example.co.uk")
expect(registrable_domain("a.foo.kawasaki.jp")).to_equal("a.foo.kawasaki.jp")
expect(registrable_domain("city.kawasaki.jp")).to_equal("city.kawasaki.jp")
expect(registrable_domain("www.city.kawasaki.jp")).to_equal("city.kawasaki.jp")
expect(registrable_domain("www.ck")).to_equal("www.ck")
expect(registrable_domain("com")).to_equal("")
expect(registrable_domain("bad..example.com")).to_equal("")
expect(registrable_domain("-bad.example.com")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/public_suffix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Public Suffix List.
- Public Suffix List

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

- Canonical SPipe generation for source `4a78fbff4004f8f393af551dea52bf2fe25e58276e697eaaf02e85836647fd94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a78fbff4004f8f393af551dea52bf2fe25e58276e697eaaf02e85836647fd94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a78fbff4004f8f393af551dea52bf2fe25e58276e697eaaf02e85836647fd94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/web/public_suffix_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/public_suffix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/public_suffix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/public_suffix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/public_suffix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/public_suffix_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact private wildcard exception and IDNA rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/public_suffix_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the registrable domain and rejects unusable hosts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
