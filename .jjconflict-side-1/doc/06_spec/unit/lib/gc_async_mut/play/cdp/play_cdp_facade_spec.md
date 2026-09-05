# Play Cdp Facade Specification

> Tests covering gc_async_mut play cdp facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Play Cdp Facade Specification

## Scenarios

### gc_async_mut play cdp facade

#### re-exports pure CDP URL and frame helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports pure CDP URL and frame helpers
   - Expected: parsed.0 equals `127.0.0.1`
   - Expected: parsed.1 equals `9222`
   - Expected: parsed.2 equals `/devtools/page/abc`
   - Expected: parsed.3 is false
   - Expected: frame.parsed is true
   - Expected: frame.opcode equals `WS_OP_TEXT`
   - Expected: frame.payload.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports pure CDP URL and frame helpers")
val parsed = cdp_parse_ws_url("ws://127.0.0.1:9222/devtools/page/abc")
expect(parsed.0).to_equal("127.0.0.1")
expect(parsed.1).to_equal(9222)
expect(parsed.2).to_equal("/devtools/page/abc")
expect(parsed.3).to_equal(false)

val frame = cdp_parse_frame([WS_FIN | WS_OP_TEXT, 2, 111, 107])
expect(frame.parsed).to_equal(true)
expect(frame.opcode).to_equal(WS_OP_TEXT)
expect(frame.payload.length()).to_equal(2)
```

</details>

#### re-exports CDP domain constants and modifier helpers

- re-exports CDP domain constants and modifier helpers
   - Expected: CDP_DEFAULT_TIMEOUT equals `10000`
   - Expected: cdp_modifiers_from(["alt", "control", "shift"]) equals `CDP_MOD_ALT | CDP_MOD_CTRL | CDP_MOD_SHIFT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports CDP domain constants and modifier helpers")
expect(CDP_DEFAULT_TIMEOUT).to_equal(10000)
expect(cdp_modifiers_from(["alt", "control", "shift"])).to_equal(CDP_MOD_ALT | CDP_MOD_CTRL | CDP_MOD_SHIFT)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut play cdp facade.
- gc_async_mut play cdp facade

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `57669a02e345e8820cce11c8fbfca36994f1fd933bfee06d6b78b12552c00224`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57669a02e345e8820cce11c8fbfca36994f1fd933bfee06d6b78b12552c00224`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57669a02e345e8820cce11c8fbfca36994f1fd933bfee06d6b78b12552c00224`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports pure CDP URL and frame helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports CDP domain constants and modifier helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
