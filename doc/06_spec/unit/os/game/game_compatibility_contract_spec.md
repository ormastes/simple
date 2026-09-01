# Game Compatibility Contract Specification

> Tests covering SimpleOS game compatibility platform contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game Compatibility Contract Specification

## Scenarios

### SimpleOS game compatibility platform contract

#### requires Linux ABI before native Linux games are ready

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires Linux ABI before native Linux games are ready
   - Expected: game_target_ready(missing_linux) is false
   - Expected: game_target_blocker(missing_linux) equals `missing-linux-abi`
   - Expected: game_target_ready(ready_linux) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires Linux ABI before native Linux games are ready")
val missing_linux = game_target_native_linux(false, true, true, true, true, true)
val ready_linux = game_target_native_linux(true, true, true, true, true, true)
expect(game_target_ready(missing_linux)).to_equal(false)
expect(game_target_blocker(missing_linux)).to_equal("missing-linux-abi")
expect(game_target_ready(ready_linux)).to_equal(true)
expect(game_target_marker(ready_linux)).to_contain("[game-platform] target=native-linux blocker=ready")
```

</details>

#### requires Steam Runtime before Steam Linux games are ready

- requires Steam Runtime before Steam Linux games are ready
   - Expected: game_target_blocker(no_runtime) equals `missing-steam-runtime`
   - Expected: game_target_ready(ready_runtime) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires Steam Runtime before Steam Linux games are ready")
val no_runtime = game_target_steam_linux(true, true, true, true, true, true, false)
val ready_runtime = game_target_steam_linux(true, true, true, true, true, true, true)
expect(game_target_blocker(no_runtime)).to_equal("missing-steam-runtime")
expect(game_target_ready(ready_runtime)).to_equal(true)
```

</details>

#### requires Proton host after Linux, Vulkan, audio, input, prefix, network, and Steam Runtime

- requires Proton host after Linux, Vulkan, audio, input, prefix, network, and Steam Runtime
   - Expected: game_target_blocker(no_vulkan) equals `missing-vulkan`
   - Expected: game_target_blocker(no_proton) equals `missing-proton-host`
   - Expected: game_target_ready(ready_proton) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires Proton host after Linux, Vulkan, audio, input, prefix, network, and Steam Runtime")
val no_vulkan = game_target_proton_x86(true, false, true, true, true, true, true, true)
val no_proton = game_target_proton_x86(true, true, true, true, true, true, true, false)
val ready_proton = game_target_proton_x86(true, true, true, true, true, true, true, true)
expect(game_target_blocker(no_vulkan)).to_equal("missing-vulkan")
expect(game_target_blocker(no_proton)).to_equal("missing-proton-host")
expect(game_target_ready(ready_proton)).to_equal(true)
```

</details>

#### blocks translated Proton on CPU translation

- blocks translated Proton on CPU translation
   - Expected: game_target_ready(translated) is false
   - Expected: game_target_blocker(translated) equals `missing-cpu-translation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks translated Proton on CPU translation")
val translated = game_target_proton_translated(true, true, true, true, true, true, true, true, false)
expect(game_target_ready(translated)).to_equal(false)
expect(game_target_blocker(translated)).to_equal("missing-cpu-translation")
```

</details>

#### allows Simple-native games without Linux ABI

- allows Simple-native games without Linux ABI
   - Expected: game_target_ready(simple_native) is true
   - Expected: game_target_blocker(simple_native) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows Simple-native games without Linux ABI")
val simple_native = game_target_simple_native(true, true, true, true, true)
expect(game_target_ready(simple_native)).to_equal(true)
expect(game_target_blocker(simple_native)).to_equal("ready")
```

</details>

#### requires full game prefix layout

- requires full game prefix layout
   - Expected: game_runtime_prefix_ready(partial) is false
   - Expected: game_runtime_prefix_blocker(partial) equals `missing-shadercache:/games/app_123456/shadercache`
   - Expected: game_runtime_prefix_ready(full) is true
   - Expected: game_runtime_prefix_blocker(full) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires full game prefix layout")
val partial = game_runtime_prefix("123456", true, true, false, true, true, true)
val full = game_runtime_prefix("123456", true, true, true, true, true, true)
expect(game_runtime_prefix_ready(partial)).to_equal(false)
expect(game_runtime_prefix_blocker(partial)).to_equal("missing-shadercache:/games/app_123456/shadercache")
expect(game_runtime_prefix_ready(full)).to_equal(true)
expect(game_runtime_prefix_blocker(full)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/game/game_compatibility_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS game compatibility platform contract.
- SimpleOS game compatibility platform contract

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

- Canonical SPipe generation for source `e7103a9876ddc0c56cf7f9e72be7652aadc9ed704c8c31cdc670e69afc017a38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7103a9876ddc0c56cf7f9e72be7652aadc9ed704c8c31cdc670e69afc017a38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7103a9876ddc0c56cf7f9e72be7652aadc9ed704c8c31cdc670e69afc017a38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/game/game_compatibility_contract_spec.spl
mirror: doc/06_spec/unit/os/game/game_compatibility_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/game/game_compatibility_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/game/game_compatibility_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/game/game_compatibility_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires Linux ABI before native Linux games are ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/game/game_compatibility_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires Steam Runtime before Steam Linux games are ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/game/game_compatibility_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires Proton host after Linux, Vulkan, audio, input, prefix, network, and Steam Runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
