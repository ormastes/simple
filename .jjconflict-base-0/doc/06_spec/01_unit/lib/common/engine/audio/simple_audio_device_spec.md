# Simple Audio Device Specification

> Tests covering pure-Simple audio device lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Audio Device Specification

## Scenarios

### pure-Simple audio device lifecycle

#### owns open negotiation playback capture stop and close

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- owns open negotiation playback capture stop and close
   - Expected: device.open(true) equals `opened`
   - Expected: device.negotiate(48000, 2, 256) equals `negotiated`
   - Expected: device.start(true, true) equals `started`
   - Expected: device.report_xrun("underrun") equals `underrun`
   - Expected: device.xrun_count equals `1`
   - Expected: device.stop() equals `stopped`
   - Expected: device.close() equals `closed`
   - Expected: device.live_resources equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("owns open negotiation playback capture stop and close")
var device = SimpleAudioDevice.create("linux", "pipewire", true, true)
expect(device.open(true)).to_equal("opened")
expect(device.negotiate(48000, 2, 256)).to_equal("negotiated")
expect(device.start(true, true)).to_equal("started")
expect(device.report_xrun("underrun")).to_equal("underrun")
expect(device.xrun_count).to_equal(1)
expect(device.stop()).to_equal("stopped")
expect(device.close()).to_equal("closed")
expect(device.live_resources).to_equal(0)
```

</details>

#### rejects unavailable ABI invalid formats and unsupported directions

- rejects unavailable ABI invalid formats and unsupported directions
   - Expected: unavailable.open(false) equals `unavailable`
   - Expected: playback_only.open(true) equals `opened`
   - Expected: playback_only.negotiate(0, 2, 256) equals `invalid-format`
   - Expected: playback_only.negotiate(48000, 2, 256) equals `negotiated`
   - Expected: playback_only.start(false, true) equals `unsupported-capture`
   - Expected: playback_only.start(false, false) equals `invalid-direction`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unavailable ABI invalid formats and unsupported directions")
var unavailable = SimpleAudioDevice.create("macos", "coreaudio", true, true)
expect(unavailable.open(false)).to_equal("unavailable")
var playback_only = SimpleAudioDevice.create("qemu", "legacy", true, false)
expect(playback_only.open(true)).to_equal("opened")
expect(playback_only.negotiate(0, 2, 256)).to_equal("invalid-format")
expect(playback_only.negotiate(48000, 2, 256)).to_equal("negotiated")
expect(playback_only.start(false, true)).to_equal("unsupported-capture")
expect(playback_only.start(false, false)).to_equal("invalid-direction")
```

</details>

#### invalidates generations on device loss and releases resources

- invalidates generations on device loss and releases resources
   - Expected: device.open(true) equals `opened`
   - Expected: device.negotiate(48000, 2, 480) equals `negotiated`
   - Expected: device.start(true, false) equals `started`
   - Expected: device.device_lost() equals `disconnected`
   - Expected: device.generation equals `opened_generation + 1u64`
   - Expected: device.stop() equals `stopped`
   - Expected: device.close() equals `closed`
   - Expected: device.live_resources equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invalidates generations on device loss and releases resources")
var device = SimpleAudioDevice.create("windows", "wasapi", true, true)
expect(device.open(true)).to_equal("opened")
val opened_generation = device.generation
expect(device.negotiate(48000, 2, 480)).to_equal("negotiated")
expect(device.start(true, false)).to_equal("started")
expect(device.device_lost()).to_equal("disconnected")
expect(device.generation).to_equal(opened_generation + 1u64)
expect(device.stop()).to_equal("stopped")
expect(device.close()).to_equal("closed")
expect(device.live_resources).to_equal(0)
```

</details>

#### selects explicit platform backends without aliases

- selects explicit platform backends without aliases
   - Expected: simple_audio_platform_backend("linux") equals `pipewire`
   - Expected: simple_audio_platform_backend("macos") equals `coreaudio`
   - Expected: simple_audio_platform_backend("windows") equals `wasapi`
   - Expected: simple_audio_platform_backend("openbsd") equals `sndio`
   - Expected: simple_audio_platform_backend("freebsd") equals `oss`
   - Expected: simple_audio_platform_backend("simpleos") equals `virtio-snd`
   - Expected: simple_audio_platform_backend("plan9") equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selects explicit platform backends without aliases")
expect(simple_audio_platform_backend("linux")).to_equal("pipewire")
expect(simple_audio_platform_backend("macos")).to_equal("coreaudio")
expect(simple_audio_platform_backend("windows")).to_equal("wasapi")
expect(simple_audio_platform_backend("openbsd")).to_equal("sndio")
expect(simple_audio_platform_backend("freebsd")).to_equal("oss")
expect(simple_audio_platform_backend("simpleos")).to_equal("virtio-snd")
expect(simple_audio_platform_backend("plan9")).to_equal("unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple audio device lifecycle.
- pure-Simple audio device lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-004`
- `REQ-005`
- `REQ-008`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c27dfc0b254c3f180f675959b58f501fad175d20bdd80f79ec04516ef9c12f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c27dfc0b254c3f180f675959b58f501fad175d20bdd80f79ec04516ef9c12f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c27dfc0b254c3f180f675959b58f501fad175d20bdd80f79ec04516ef9c12f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl
mirror: doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_device_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_device_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_device_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns open negotiation playback capture stop and close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unavailable ABI invalid formats and unsupported directions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates generations on device loss and releases resources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
