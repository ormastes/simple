# `url_encode` percent-encoding under the interpreter

> Anyone building a URL or query string from user data via

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `url_encode` percent-encoding under the interpreter

Anyone building a URL or query string from user data via

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Anyone building a URL or query string from user data via
`std.nogc_sync_mut.http_client.types.url_encode`. This spec exists because
`doc/08_tracking/bug/interp_http_url_encode_utilities_unresolved_2026-06-14.md`
was closed with no surviving covering spec: `url_encode` used to be entirely
unusable under the interpreter, with the calling function dying silently after
`[WARN] Failed to load export source error=semantic: Cannot resolve module:
utilities`.

## Scope and Preconditions

Pure function, no host state. The original defect was a MODULE RESOLUTION
failure, so the load-bearing part of this spec is that the import resolves and
the function returns at all -- silent death, not a wrong value, was the
symptom. The value assertions guard the encoding itself.

## Primary Workflow

Encode strings containing characters that must be escaped in a URL, and confirm
unreserved characters are passed through untouched.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Unreserved | `A-Z a-z 0-9 - _ . ~` survive encoding unchanged |
| Percent-encoding | Everything else becomes `%HH` with uppercase hex |

## Related Specifications

- `doc/08_tracking/bug/interp_http_url_encode_utilities_unresolved_2026-06-14.md`

## Scenarios

### url_encode percent-encodes reserved characters

#### encodes the at-sign in an email address

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes the at-sign in an email address
- Encode the address from the original bug report
   - Expected: url_encode("ops@acme.com") equals `ops%40acme.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes the at-sign in an email address")
step("Encode the address from the original bug report")
# This exact call is what used to die silently after printing CLIENT_OK.
expect(url_encode("ops@acme.com")).to_equal("ops%40acme.com")
```

</details>

#### passes unreserved characters through unchanged

- passes unreserved characters through unchanged
- Encode a string made only of unreserved characters
   - Expected: url_encode("abcXYZ019") equals `abcXYZ019`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes unreserved characters through unchanged")
step("Encode a string made only of unreserved characters")
expect(url_encode("abcXYZ019")).to_equal("abcXYZ019")
```

</details>

#### encodes a space

- encodes a space
- Encode a value containing a space
   - Expected: url_encode("a b") equals `a%20b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes a space")
step("Encode a value containing a space")
expect(url_encode("a b")).to_equal("a%20b")
```

</details>

#### encodes characters that would otherwise break a query string

- encodes characters that would otherwise break a query string
- Encode the query delimiters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes characters that would otherwise break a query string")
step("Encode the query delimiters")
expect(url_encode("a&b")).to_contain("%26")
expect(url_encode("a=b")).to_contain("%3D")
```

</details>

#### returns an empty string for empty input

- returns an empty string for empty input
- Encode the empty string
   - Expected: url_encode("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an empty string for empty input")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-HTTP-URLENCODE-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d04dfcae6e8230bf5959040055e50a5277832234548e774379c368341ba24341`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d04dfcae6e8230bf5959040055e50a5277832234548e774379c368341ba24341`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d04dfcae6e8230bf5959040055e50a5277832234548e774379c368341ba24341`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes the at-sign in an email address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes unreserved characters through unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http_client/url_encode_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes a space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
