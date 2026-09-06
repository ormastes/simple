# Steam 2048 Demo Specification

> Tests covering SimpleOS Steam 2048 smoke game.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steam 2048 Demo Specification

## Scenarios

### SimpleOS Steam 2048 smoke game

#### keeps the deterministic 2048 merge rule executable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the deterministic 2048 merge rule executable
   - Expected: steam_2048_row_text(merged) equals `4,0,0,0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the deterministic 2048 merge rule executable")
val merged = steam_2048_merge_left([2, 2, 0, 0])
expect(steam_2048_row_text(merged)).to_equal("4,0,0,0")
```

</details>

#### binds the open source 2048 game to the Steam facade

- binds the open source 2048 game to the Steam facade
   - Expected: run.source_game equals `2048`
   - Expected: run.upstream_url equals `https://github.com/gabrielecirulli/2048`
   - Expected: run.license equals `MIT`
   - Expected: run.steam.state.achievement_unlocked is true
   - Expected: run.steam.state.drm_ticket equals `simple-drm-ticket`
   - Expected: run.port_profile.profile_version equals `steamos-rebuild-v1`
   - Expected: run.port_profile.rebuild_target equals `simpleos-native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds the open source 2048 game to the Steam facade")
val run = steam_2048_demo_run()
expect(run.source_game).to_equal("2048")
expect(run.upstream_url).to_equal("https://github.com/gabrielecirulli/2048")
expect(run.license).to_equal("MIT")
expect(run.steam.state.achievement_unlocked).to_equal(true)
expect(run.steam.state.drm_ticket).to_equal("simple-drm-ticket")
expect(run.port_profile.profile_version).to_equal("steamos-rebuild-v1")
expect(run.port_profile.rebuild_target).to_equal("simpleos-native")
```

</details>

#### emits a guest-checkable marker

- emits a guest-checkable marker
   - Expected: steam_2048_simpleos_guest_marker_ready(marker) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a guest-checkable marker")
val marker = steam_2048_demo_marker()
expect(marker).to_contain("[steam-2048-demo]")
expect(marker).to_contain("runtime=SteamLinuxRuntime/soldier")
expect(marker).to_contain("network=true")
expect(steam_2048_simpleos_guest_marker_ready(marker)).to_equal(true)
```

</details>

#### emits a rebuild-porting manifest and marker

- emits a rebuild-porting manifest and marker
   - Expected: steam_2048_port_guest_marker_ready(marker) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a rebuild-porting manifest and marker")
val manifest = steam_2048_port_manifest()
val marker = steam_2048_port_marker()
expect(manifest).to_contain("port_profile=steamos-rebuild-v1")
expect(manifest).to_contain("source=2048")
expect(manifest).to_contain("rebuild_target=simpleos-native")
expect(marker).to_contain("steam_facade=simple-steam-sffi-v1")
expect(steam_2048_port_guest_marker_ready(marker)).to_equal(true)
```

</details>

#### rejects incomplete guest serial evidence

- rejects incomplete guest serial evidence
   - Expected: steam_2048_simpleos_guest_marker_ready("[steam-2048-demo] source=2048") is false
   - Expected: steam_2048_port_guest_marker_ready("[game-port] profile=steamos-rebuild-v1 source=2048") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects incomplete guest serial evidence")
expect(steam_2048_simpleos_guest_marker_ready("[steam-2048-demo] source=2048")).to_equal(false)
expect(steam_2048_port_guest_marker_ready("[game-port] profile=steamos-rebuild-v1 source=2048")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/game/steam_2048_demo_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Steam 2048 smoke game.
- SimpleOS Steam 2048 smoke game

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99bf6fcd304880945e0344822614fe72fa7ac41e75fad5745d773c176a1c95b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99bf6fcd304880945e0344822614fe72fa7ac41e75fad5745d773c176a1c95b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99bf6fcd304880945e0344822614fe72fa7ac41e75fad5745d773c176a1c95b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/game/steam_2048_demo_spec.spl
mirror: doc/06_spec/unit/os/game/steam_2048_demo_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/game/steam_2048_demo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/game/steam_2048_demo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/game/steam_2048_demo_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the deterministic 2048 merge rule executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/game/steam_2048_demo_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the open source 2048 game to the Steam facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/game/steam_2048_demo_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a guest-checkable marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
