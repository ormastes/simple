# `url_encode` percent-encoding under the interpreter

> Verifies the url encode behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `url_encode` percent-encoding under the interpreter

Verifies the url encode behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the url encode behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### url_encode percent-encodes reserved characters

#### encodes the at-sign in an email address

- Verify: encodes the at-sign in an email address
- Encode the address from the original bug report
   - Expected: url_encode("ops@acme.com") equals `ops%40acme.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-HTTP-URLENCODE-001
step("Verify: encodes the at-sign in an email address")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Encode the address from the original bug report")
# This exact call is what used to die silently after printing CLIENT_OK.
expect(url_encode("ops@acme.com")).to_equal("ops%40acme.com")
```

</details>

#### passes unreserved characters through unchanged

- Verify: passes unreserved characters through unchanged
- Encode a string made only of unreserved characters
   - Expected: url_encode("abcXYZ019") equals `abcXYZ019`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-HTTP-URLENCODE-001
step("Verify: passes unreserved characters through unchanged")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Encode a string made only of unreserved characters")
expect(url_encode("abcXYZ019")).to_equal("abcXYZ019")
```

</details>

#### encodes a space

- Verify: encodes a space
- Encode a value containing a space
   - Expected: url_encode("a b") equals `a%20b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-HTTP-URLENCODE-001
step("Verify: encodes a space")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Encode a value containing a space")
expect(url_encode("a b")).to_equal("a%20b")
```

</details>

#### encodes characters that would otherwise break a query string

- Verify: encodes characters that would otherwise break a query string
- Encode the query delimiters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-HTTP-URLENCODE-001
step("Verify: encodes characters that would otherwise break a query string")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Encode the query delimiters")
expect(url_encode("a&b")).to_contain("%26")
expect(url_encode("a=b")).to_contain("%3D")
```

</details>

#### returns an empty string for empty input

- Verify: returns an empty string for empty input
- Encode the empty string
   - Expected: url_encode("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-HTTP-URLENCODE-001
step("Verify: returns an empty string for empty input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Encode the empty string")
expect(url_encode("")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d2b96a8b69b6528a69cb769abea40afdf47bfcf16d90331bb0ade6d831a24d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d2b96a8b69b6528a69cb769abea40afdf47bfcf16d90331bb0ade6d831a24d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d2b96a8b69b6528a69cb769abea40afdf47bfcf16d90331bb0ade6d831a24d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
