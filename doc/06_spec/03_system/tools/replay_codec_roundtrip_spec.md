# Replay Codec Roundtrip Specification

> Tests covering ReplayEntry codec roundtrip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Codec Roundtrip Specification

## Scenarios

### ReplayEntry codec roundtrip

#### encode then decode preserves event_id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encode then decode preserves event_id
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encode then decode preserves event_id")
val e = ReplayEntry.create(EventKind.Schedule, 10, 20, 0)
val bytes = encode_entry(e)
val r = decode_entry(bytes, 0)
var ok = false
if val Ok(de) = r:
    ok = de.event_id == e.event_id
expect(ok).to_equal(true)
```

</details>

#### encode then decode preserves thread_id

- encode then decode preserves thread_id
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encode then decode preserves thread_id")
val e = ReplayEntry.create(EventKind.SyscallEnter, 42, 1, 0)
val bytes = encode_entry(e)
val r = decode_entry(bytes, 0)
var ok = false
if val Ok(de) = r:
    ok = de.thread_id == 42
expect(ok).to_equal(true)
```

</details>

#### encode then decode preserves kind

- encode then decode preserves kind
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encode then decode preserves kind")
val e = ReplayEntry.create(EventKind.IpcSend, 5, 1, 0)
val bytes = encode_entry(e)
val r = decode_entry(bytes, 0)
var ok = false
if val Ok(de) = r:
    ok = de.kind == EventKind.IpcSend.to_i32()
expect(ok).to_equal(true)
```

</details>

#### encode produces 80 bytes

- encode produces 80 bytes
   - Expected: bytes.len() equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encode produces 80 bytes")
val e = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
val bytes = encode_entry(e)
expect(bytes.len()).to_equal(80)
```

</details>

#### decode_entry on insufficient bytes returns Err

- decode_entry on insufficient bytes returns Err
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decode_entry on insufficient bytes returns Err")
val short: [i32] = [0, 1, 2]
val r = decode_entry(short, 0)
var is_err = true
if val Ok(_) = r:
    is_err = false
expect(is_err).to_equal(true)
```

</details>

#### encode_entries then decode_entries roundtrips two events

- encode_entries then decode_entries roundtrips two events
   - Expected: decoded.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encode_entries then decode_entries roundtrips two events")
val e1 = ReplayEntry.create(EventKind.ThreadCreate, 11, 1, 0)
val e2 = ReplayEntry.create(EventKind.ThreadExit, 12, 1, 0)
val entries = [e1, e2]
val bytes = encode_entries(entries)
val decoded = decode_entries(bytes)
expect(decoded.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_codec_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ReplayEntry codec roundtrip.
- ReplayEntry codec roundtrip

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `566f3fbc166d22bd4d763047938b4eda6260e85b95f07263b0d8c04b5809442d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `566f3fbc166d22bd4d763047938b4eda6260e85b95f07263b0d8c04b5809442d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `566f3fbc166d22bd4d763047938b4eda6260e85b95f07263b0d8c04b5809442d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/replay_codec_roundtrip_spec.spl
mirror: doc/06_spec/03_system/tools/replay_codec_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/replay_codec_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/replay_codec_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/replay_codec_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/replay_codec_roundtrip_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encode then decode preserves event_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_codec_roundtrip_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encode then decode preserves thread_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_codec_roundtrip_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encode then decode preserves kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
