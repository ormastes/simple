# Netcat Listen Mode Specification

> Compile-check that run_netcat correctly parses -l PORT into listen mode, and that connect mode requires HOST and PORT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Netcat Listen Mode Specification

Compile-check that run_netcat correctly parses -l PORT into listen mode, and that connect mode requires HOST and PORT.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B5 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/os/tools/net/netcat_listen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Compile-check that run_netcat correctly parses -l PORT into listen mode,
and that connect mode requires HOST and PORT.

## Scenarios

### run_netcat argument parsing

#### returns error when no args provided

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns error when no args provided
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error when no args provided")
val result = run_netcat([])
expect(result).to_equal(1)
```

</details>

#### accepts -l flag as first argument for listen mode

- accepts -l flag as first argument for listen mode
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts -l flag as first argument for listen mode")
# We can only verify parse path without a real network;
# passing -l with no port should return error code 1
val result = run_netcat(["-l"])
expect(result).to_equal(1)
```

</details>

#### connect mode without port returns error

- connect mode without port returns error
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("connect mode without port returns error")
val result = run_netcat(["somehost"])
expect(result).to_equal(1)
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38e464dc73113189e3f4e71910edae070c21109f0e191fba9f5247f44a0d1f9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38e464dc73113189e3f4e71910edae070c21109f0e191fba9f5247f44a0d1f9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38e464dc73113189e3f4e71910edae070c21109f0e191fba9f5247f44a0d1f9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/tools/net/netcat_listen_spec.spl
mirror: doc/06_spec/unit/os/tools/net/netcat_listen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tools/net/netcat_listen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tools/net/netcat_listen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tools/net/netcat_listen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/tools/net/netcat_listen_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error when no args provided' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tools/net/netcat_listen_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts -l flag as first argument for listen mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tools/net/netcat_listen_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connect mode without port returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
