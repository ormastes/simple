# Cli Extension Wire Fail Closed Specification

> Tests covering SimpleCliExtensionV1 validate — fail-closed with positive control.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Extension Wire Fail Closed Specification

## Scenarios

### SimpleCliExtensionV1 validate — fail-closed with positive control

#### rejects an unknown namespace while accepting the valid sibling

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an unknown namespace while accepting the valid sibling
   - Expected: _verdict(ext, "--xnet-level=debug") contains `unknown namespace`
   - Expected: _verdict(ext, "--xlog-level=debug") equals `"")  # positive control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown namespace while accepting the valid sibling")
val ext = _ext()
expect(_verdict(ext, "--xnet-level=debug").contains("unknown namespace")).to_equal(true)
expect(_verdict(ext, "--xlog-level=debug")).to_equal("")  # positive control
```

</details>

#### rejects an undeclared key while accepting the valid sibling

- rejects an undeclared key while accepting the valid sibling
   - Expected: _verdict(ext, "--xlog-verbose") contains `unknown option key`
   - Expected: _verdict(ext, "--xlog-color") equals `"")  # positive control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an undeclared key while accepting the valid sibling")
val ext = _ext()
expect(_verdict(ext, "--xlog-verbose").contains("unknown option key")).to_equal(true)
expect(_verdict(ext, "--xlog-color")).to_equal("")  # positive control
```

</details>

#### rejects a value outside the closed set while accepting an allowed one

- rejects a value outside the closed set while accepting an allowed one
   - Expected: _verdict(ext, "--xlog-level=chatty") contains `not allowed`
   - Expected: _verdict(ext, "--xlog-level=warn") equals `"")  # positive control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a value outside the closed set while accepting an allowed one")
val ext = _ext()
expect(_verdict(ext, "--xlog-level=chatty").contains("not allowed")).to_equal(true)
expect(_verdict(ext, "--xlog-level=warn")).to_equal("")  # positive control
```

</details>

#### rejects arity misuse both ways while accepting the correct forms

- rejects arity misuse both ways while accepting the correct forms
   - Expected: _verdict(ext, "--xlog-color=on") contains `takes no value`
   - Expected: _verdict(ext, "--xlog-level") contains `requires =<value>`
   - Expected: _verdict(ext, "--xlog-color") equals `"")        # positive control`
   - Expected: _verdict(ext, "--xlog-level=info") equals `"")   # positive control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects arity misuse both ways while accepting the correct forms")
val ext = _ext()
expect(_verdict(ext, "--xlog-color=on").contains("takes no value")).to_equal(true)
expect(_verdict(ext, "--xlog-level").contains("requires =<value>")).to_equal(true)
expect(_verdict(ext, "--xlog-color")).to_equal("")        # positive control
expect(_verdict(ext, "--xlog-level=info")).to_equal("")   # positive control
```

</details>

#### rejects non-extension and malformed tokens

- rejects non-extension and malformed tokens
   - Expected: _verdict(ext, "--help") != "" is true
   - Expected: _verdict(ext, "plain-arg") != "" is true
   - Expected: _verdict(ext, "--xLOG-level=debug") != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-extension and malformed tokens")
val ext = _ext()
expect(_verdict(ext, "--help") != "").to_equal(true)
expect(_verdict(ext, "plain-arg") != "").to_equal(true)
expect(_verdict(ext, "--xLOG-level=debug") != "").to_equal(true)
```

</details>

#### fails closed on a bad config: wrong schema and duplicate keys rejected, valid config accepted

- fails closed on a bad config: wrong schema and duplicate keys rejected, valid config accepted
   - Expected: good.ns equals `"log")  # positive control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a bad config: wrong schema and duplicate keys rejected, valid config accepted")
val bad_schema = "schema: simple.other/9\nnamespace: log\nprovider_id: p\noptions:\n  - key: a\n    kind: flag\n"
match cli_extension_from_sdn_v1(bad_schema):
    case Ok(_): expect("accepted wrong schema").to_equal("")
    case Err(e): expect(e.contains("unsupported schema")).to_equal(true)
var dup = "schema: simple.cli_extension_wire/1\nnamespace: log\nprovider_id: p\noptions:\n"
dup = dup + "  - key: a\n    kind: flag\n  - key: a\n    kind: flag\n"
match cli_extension_from_sdn_v1(dup):
    case Ok(_): expect("accepted duplicate key").to_equal("")
    case Err(e): expect(e.contains("duplicate option key")).to_equal(true)
val good = _ext()
expect(good.ns).to_equal("log")  # positive control
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleCliExtensionV1 validate — fail-closed with positive control.
- SimpleCliExtensionV1 validate — fail-closed with positive control

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `567fd7afbe26b1134faec7491db6724ca3cc84f8b02433f3088686bc760875a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `567fd7afbe26b1134faec7491db6724ca3cc84f8b02433f3088686bc760875a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `567fd7afbe26b1134faec7491db6724ca3cc84f8b02433f3088686bc760875a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown namespace while accepting the valid sibling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an undeclared key while accepting the valid sibling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/cli_extension_wire_fail_closed_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a value outside the closed set while accepting an allowed one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
