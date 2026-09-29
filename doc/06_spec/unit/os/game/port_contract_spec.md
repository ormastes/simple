# Port Contract Specification

> Tests covering MDSOC game port contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Port Contract Specification

## Scenarios

### MDSOC game port contract

#### defines the common rebuild profile outside Steam implementation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines the common rebuild profile outside Steam implementation
   - Expected: profile.profile_version equals `steamos-rebuild-v1`
   - Expected: profile.rebuild_target equals `simpleos-native`
   - Expected: profile.graphics_api equals `sdl2_subset`
   - Expected: profile.steam_facade_abi equals `simple-steam-sffi-v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines the common rebuild profile outside Steam implementation")
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
expect(profile.profile_version).to_equal("steamos-rebuild-v1")
expect(profile.rebuild_target).to_equal("simpleos-native")
expect(profile.graphics_api).to_equal("sdl2_subset")
expect(profile.steam_facade_abi).to_equal("simple-steam-sffi-v1")
```

</details>

#### probes required rebuild capabilities

- probes required rebuild capabilities
   - Expected: readiness.ready is true
   - Expected: readiness.matched_count equals `readiness.required_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probes required rebuild capabilities")
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
val readiness = game_port_probe(profile, game_port_core_capabilities())
expect(readiness.ready).to_equal(true)
expect(readiness.matched_count).to_equal(readiness.required_count)
```

</details>

#### fails closed when the rebuild toolchain contract is missing

- fails closed when the rebuild toolchain contract is missing
   - Expected: readiness.ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when the rebuild toolchain contract is missing")
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
val readiness = game_port_probe(profile, ["simpleos_smf_packaging"])
expect(readiness.ready).to_equal(false)
expect(readiness.blocker).to_contain("simple_native_rebuild")
```

</details>

#### emits a package manifest and guest marker

- emits a package manifest and guest marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a package manifest and guest marker")
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
val readiness = game_port_probe(profile, game_port_core_capabilities())
val manifest = game_port_manifest(profile)
val marker = game_port_marker(profile, readiness)
expect(manifest).to_contain("port_profile=steamos-rebuild-v1")
expect(manifest).to_contain("upstream=https://github.com/gabrielecirulli/2048")
expect(manifest).to_contain("steam_facade=simple-steam-sffi-v1")
expect(marker).to_contain("[game-port]")
expect(marker).to_contain("ready=true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/game/port_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MDSOC game port contract.
- MDSOC game port contract

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33217e6a133d01d072e458483ca48936bcb243cf31794a9a3fe51842c7365230`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33217e6a133d01d072e458483ca48936bcb243cf31794a9a3fe51842c7365230`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33217e6a133d01d072e458483ca48936bcb243cf31794a9a3fe51842c7365230`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/game/port_contract_spec.spl
mirror: doc/06_spec/unit/os/game/port_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/game/port_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/game/port_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/game/port_contract_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines the common rebuild profile outside Steam implementation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/game/port_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probes required rebuild capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/game/port_contract_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when the rebuild toolchain contract is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
