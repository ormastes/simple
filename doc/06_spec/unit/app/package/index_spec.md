# Index Specification

> Tests covering index_path_for, parse_token_from_sdn.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Index Specification

## Scenarios

### index_path_for

#### handles standard 4+ char names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles standard 4+ char names
   - Expected: path equals `ht/tp/http.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles standard 4+ char names")
val path = index_path_for("http")
expect(path).to_equal("ht/tp/http.sdn")
```

</details>

#### handles 3 char names

- handles 3 char names
   - Expected: path equals `ur/l/url.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles 3 char names")
val path = index_path_for("url")
expect(path).to_equal("ur/l/url.sdn")
```

</details>

#### handles 2 char names

- handles 2 char names
   - Expected: path equals `i/o/io.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles 2 char names")
val path = index_path_for("io")
expect(path).to_equal("i/o/io.sdn")
```

</details>

#### handles 1 char names

- handles 1 char names
   - Expected: path equals `_/x/x.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles 1 char names")
val path = index_path_for("x")
expect(path).to_equal("_/x/x.sdn")
```

</details>

#### handles long names

- handles long names
   - Expected: path equals `co/ll/collections.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles long names")
val path = index_path_for("collections")
expect(path).to_equal("co/ll/collections.sdn")
```

</details>

### parse_token_from_sdn

#### extracts token from credentials file

- extracts token from credentials file
   - Expected: token equals `ghp-abc123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts token from credentials file")
val content = "registry:\n  token: ghp-abc123\n  type: github_pat\n"
val token = parse_token("token:", content)
expect(token).to_equal("ghp-abc123")
```

</details>

#### returns empty for missing token

- returns empty for missing token
   - Expected: token equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing token")
val content = "registry:\n  type: github_pat\n"
val token = parse_token("token:", content)
expect(token).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/package/index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering index_path_for, parse_token_from_sdn.
- index_path_for
- parse_token_from_sdn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `3d1aa3db748d7718c76d82e4871e4bda22db940c2dfb6aee7424fac2ce621112`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d1aa3db748d7718c76d82e4871e4bda22db940c2dfb6aee7424fac2ce621112`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d1aa3db748d7718c76d82e4871e4bda22db940c2dfb6aee7424fac2ce621112`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/package/index_spec.spl
mirror: doc/06_spec/unit/app/package/index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/package/index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/package/index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/package/index_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles standard 4+ char names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/package/index_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles 3 char names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/package/index_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles 2 char names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
