# 02 T32 Open Close Specification

> Tests covering T32 hardware session open/close.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 02 T32 Open Close Specification

## Scenarios

### T32 hardware session open/close

#### successful connection

#### opens T32 session

- opens T32 session
   - Expected: client.connected is true
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("opens T32 session")
val result = t32_hw_connect()
match result:
    Ok(client):
        expect(client.connected).to_equal(true)
        client.disconnect()
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### session responds to ping

- session responds to ping
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("session responds to ping")
val result = t32_hw_connect()
match result:
    Ok(client):
        val ping = t32_hw_run_cmd(client, "PING")
        match ping:
            Ok(_): expect("ping ok").to_contain("ok")
            Err(e): expect("ping failed: {e}").to_equal("ok")
        client.disconnect()
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### evaluates VERSION.BUILD()

- evaluates VERSION.BUILD()
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("evaluates VERSION.BUILD()")
val result = t32_hw_connect()
match result:
    Ok(client):
        val ver = t32_hw_eval(client, "VERSION.BUILD()")
        match ver:
            Ok(v): expect(v.len()).to_be_greater_than(0)
            Err(e): expect("eval failed: {e}").to_equal("ok")
        client.disconnect()
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### session teardown

#### closes session cleanly

- closes session cleanly
   - Expected: client.connected is false
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("closes session cleanly")
val result = t32_hw_connect()
match result:
    Ok(client):
        client.disconnect()
        expect(client.connected).to_equal(false)
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### negative cases

#### connection fails on bad port

- connection fails on bad port


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connection fails on bad port")
val config = DebugConfig(
    host: t32_hw_host(),
    port: 19999,
    program: "",
    args: [],
    debugger: "t32",
    remote: true
)
val result = Trace32Client.connect(config)
match result:
    Ok(_): expect("should not connect").to_equal("error")
    Err(_): expect("bad port rejected").to_contain("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/02_t32_open_close_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 hardware session open/close.
- T32 hardware session open/close

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb8791a8cd86752e7ca4716b514719f7e2ead9b022902c4828c1956df0909e7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb8791a8cd86752e7ca4716b514719f7e2ead9b022902c4828c1956df0909e7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb8791a8cd86752e7ca4716b514719f7e2ead9b022902c4828c1956df0909e7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/02_t32_open_close_spec.spl
mirror: doc/06_spec/integration/t32_hw/02_t32_open_close_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/02_t32_open_close_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/02_t32_open_close_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/02_t32_open_close_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens T32 session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/02_t32_open_close_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session responds to ping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/02_t32_open_close_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates VERSION.BUILD()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
