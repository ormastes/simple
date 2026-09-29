# Steamworks Bridge Specification

> Tests covering Steamworks IPC bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steamworks Bridge Specification

## Scenarios

### Steamworks IPC bridge

#### connect with valid socket path returns is_ok=true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- connect with valid socket path returns is_ok=true
   - Expected: conn.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("connect with valid socket path returns is_ok=true")
val conn = steamworks_connect("/tmp/.steam/steam.sock")
expect(conn.is_ok).to_equal(true)
expect(conn.conn_id).to_be_greater_than(0)
```

</details>

#### connect with empty path returns error

- connect with empty path returns error
   - Expected: conn.is_ok is false
   - Expected: conn.error equals `missing-socket-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("connect with empty path returns error")
val conn = steamworks_connect("")
expect(conn.is_ok).to_equal(false)
expect(conn.error).to_equal("missing-socket-path")
```

</details>

#### two connects return distinct conn_ids

- two connects return distinct conn_ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two connects return distinct conn_ids")
val c1 = steamworks_connect("/tmp/.steam/steam.sock")
val c2 = steamworks_connect("/tmp/.steam/steam.sock")
expect(c1.conn_id).to_not_equal(c2.conn_id)
```

</details>

#### validate_app returns owned=true for non-empty app_id

- validate_app returns owned=true for non-empty app_id
   - Expected: result.is_ok is true
   - Expected: result.owned is true
   - Expected: result.app_id equals `480`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validate_app returns owned=true for non-empty app_id")
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_validate_app(conn.conn_id, "480")
expect(result.is_ok).to_equal(true)
expect(result.owned).to_equal(true)
expect(result.app_id).to_equal("480")
```

</details>

#### validate_app returns owned=false for empty app_id

- validate_app returns owned=false for empty app_id
   - Expected: result.owned is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validate_app returns owned=false for empty app_id")
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_validate_app(conn.conn_id, "")
expect(result.owned).to_equal(false)
```

</details>

#### validate_app returns is_ok=false on invalid connection

- validate_app returns is_ok=false on invalid connection
   - Expected: result.is_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validate_app returns is_ok=false on invalid connection")
val result = steamworks_validate_app(0, "480")
expect(result.is_ok).to_equal(false)
```

</details>

#### unlock_achievement returns unlocked=true for valid name

- unlock_achievement returns unlocked=true for valid name
   - Expected: result.is_ok is true
   - Expected: result.unlocked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unlock_achievement returns unlocked=true for valid name")
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_unlock_achievement(conn.conn_id, "ACH_WIN_ONE_GAME")
expect(result.is_ok).to_equal(true)
expect(result.unlocked).to_equal(true)
```

</details>

#### unlock_achievement returns unlocked=false for empty name

- unlock_achievement returns unlocked=false for empty name
   - Expected: result.unlocked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unlock_achievement returns unlocked=false for empty name")
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_unlock_achievement(conn.conn_id, "")
expect(result.unlocked).to_equal(false)
```

</details>

#### disconnect removes connection

- disconnect removes connection
   - Expected: result.is_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disconnect removes connection")
val conn = steamworks_connect("/tmp/.steam/steam.sock")
steamworks_disconnect(conn.conn_id)
val result = steamworks_validate_app(conn.conn_id, "480")
expect(result.is_ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Steamworks IPC bridge.
- Steamworks IPC bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `49d81f9ab91cfa403d704c6f73a6b991e3b0ae54de440e2ce18abede462fe234`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49d81f9ab91cfa403d704c6f73a6b991e3b0ae54de440e2ce18abede462fe234`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49d81f9ab91cfa403d704c6f73a6b991e3b0ae54de440e2ce18abede462fe234`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connect with valid socket path returns is_ok=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connect with empty path returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two connects return distinct conn_ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
