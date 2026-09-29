# LLM Profile -> Spawn Rights Adapter Specification (Production Harden, lane INT-3)

> Master plan §5.4 + §17: an LLM process's spawn-time capabilities must be its PROFILE's effective rights INTERSECTED with the parent's delegable rights and the executable ceiling — deny always wins, never amplified. This spec proves `src/os/security/llm_profiles/profile_spawn_adapter.spl` (the pure adapter bridging `profile_registry.spl`'s LLM_RIGHT_* policy rights and `spawn_authority.spl`'s CAP_RIGHT_* spawn rights) honors that law with concrete bit-value oracles:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Profile -> Spawn Rights Adapter Specification (Production Harden, lane INT-3)

Master plan §5.4 + §17: an LLM process's spawn-time capabilities must be its PROFILE's effective rights INTERSECTED with the parent's delegable rights and the executable ceiling — deny always wins, never amplified. This spec proves `src/os/security/llm_profiles/profile_spawn_adapter.spl` (the pure adapter bridging `profile_registry.spl`'s LLM_RIGHT_* policy rights and `spawn_authority.spl`'s CAP_RIGHT_* spawn rights) honors that law with concrete bit-value oracles:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-HARDEN-INT3-LLM-SPAWN-ADAPTER |
| Category | Runtime / Security |
| Difficulty | 3/5 |
| Status | Implemented |
| Plan | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane INT-3) |
| Design | doc/01_research/domain/simpleos_production_host_master_plan.md (§5.4, §17) |
| Source | `test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Master plan §5.4 + §17: an LLM process's spawn-time capabilities must be its
PROFILE's effective rights INTERSECTED with the parent's delegable rights and
the executable ceiling — deny always wins, never amplified. This spec proves
`src/os/security/llm_profiles/profile_spawn_adapter.spl` (the pure adapter
bridging `profile_registry.spl`'s LLM_RIGHT_* policy rights and
`spawn_authority.spl`'s CAP_RIGHT_* spawn rights) honors that law with
concrete bit-value oracles:

  - the final spawn rights are a subset of the parent's delegable rights, of
    the executable ceiling, AND of the profile's own mapped rights at once
    (triple attenuation);
  - a right the profile lacks never appears in the result even when both the
    parent and the executable hold it;
  - an LLM_RIGHT_* bit with no kernel-capability analogue (e.g. NET,
    PROCESS_SPAWN) contributes NO spawn right — fail-closed on unmapped bits;
  - the built-in `offline` profile produces the most restrictive spawn rights
    and `system-administration` the broadest, and both remain clamped by a
    narrow `parent_delegable`.

## Scenarios

### llm_spawn_effective_rights: triple attenuation

#### effective rights are a subset of the profile's mapped rights, parent_delegable, and executable_ceiling

- effective rights are a subset of the profile's mapped rights, parent_delegable, and executable_ceiling
- Profile grants FS_READ+FS_WRITE+FS_EXEC+DEVICE -> mapped spawn rights READ|WRITE|EXEC|MAP = 71
   - Expected: mapped equals `71u32`
- Parent only delegates READ|WRITE (3); executable ceiling only allows READ|MAP (65)
   - Expected: parent_delegable equals `3u32`
   - Expected: executable_ceiling equals `65u32`
- Only READ (1) survives all three intersections
   - Expected: eff equals `1u32`
   - Expected: spawn_rights_is_subset(eff, mapped) is true
   - Expected: spawn_rights_is_subset(eff, parent_delegable) is true
   - Expected: spawn_rights_is_subset(eff, executable_ceiling) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("effective rights are a subset of the profile's mapped rights, parent_delegable, and executable_ceiling")
step("Profile grants FS_READ+FS_WRITE+FS_EXEC+DEVICE -> mapped spawn rights READ|WRITE|EXEC|MAP = 71")
val profile = _profile(LLM_RIGHT_FS_READ | LLM_RIGHT_FS_WRITE | LLM_RIGHT_FS_EXEC | LLM_RIGHT_DEVICE)
val mapped = llm_profile_to_spawn_rights(profile)
expect(mapped).to_equal(71u32)
step("Parent only delegates READ|WRITE (3); executable ceiling only allows READ|MAP (65)")
val parent_delegable = CAP_RIGHT_READ | CAP_RIGHT_WRITE
val executable_ceiling = CAP_RIGHT_READ | CAP_RIGHT_MAP
expect(parent_delegable).to_equal(3u32)
expect(executable_ceiling).to_equal(65u32)
val eff = llm_spawn_effective_rights(profile, parent_delegable, executable_ceiling)
step("Only READ (1) survives all three intersections")
expect(eff).to_equal(1u32)
expect(spawn_rights_is_subset(eff, mapped)).to_equal(true)
expect(spawn_rights_is_subset(eff, parent_delegable)).to_equal(true)
expect(spawn_rights_is_subset(eff, executable_ceiling)).to_equal(true)
```

</details>

#### the triple-attenuation oracle holds for the same fixture

- the triple-attenuation oracle holds for the same fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the triple-attenuation oracle holds for the same fixture")
val profile = _profile(LLM_RIGHT_FS_READ | LLM_RIGHT_FS_WRITE | LLM_RIGHT_FS_EXEC | LLM_RIGHT_DEVICE)
val parent_delegable = CAP_RIGHT_READ | CAP_RIGHT_WRITE
val executable_ceiling = CAP_RIGHT_READ | CAP_RIGHT_MAP
assert_true(llm_spawn_rights_triple_attenuated(profile, parent_delegable, executable_ceiling))
```

</details>

### llm_spawn_effective_rights: profile is the ceiling too

#### WRITE never appears when the profile only holds FS_READ, despite wide-open parent and executable

- WRITE never appears when the profile only holds FS_READ, despite wide-open parent and executable
- Effective rights equal exactly READ (1), never READ|WRITE|EXEC|MAP
   - Expected: eff equals `1u32`
   - Expected: eff & CAP_RIGHT_WRITE equals `0u32`
   - Expected: eff & CAP_RIGHT_EXEC equals `0u32`
   - Expected: eff & CAP_RIGHT_MAP equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("WRITE never appears when the profile only holds FS_READ, despite wide-open parent and executable")
val profile = _profile(LLM_RIGHT_FS_READ)
val wide_open = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC | CAP_RIGHT_MAP
val eff = llm_spawn_effective_rights(profile, wide_open, wide_open)
step("Effective rights equal exactly READ (1), never READ|WRITE|EXEC|MAP")
expect(eff).to_equal(1u32)
expect(eff & CAP_RIGHT_WRITE).to_equal(0u32)
expect(eff & CAP_RIGHT_EXEC).to_equal(0u32)
expect(eff & CAP_RIGHT_MAP).to_equal(0u32)
assert_true(llm_spawn_rights_triple_attenuated(profile, wide_open, wide_open))
```

</details>

### llm_profile_to_spawn_rights: unmapped rights fail closed

#### a NET-only profile maps to zero spawn rights

- a NET-only profile maps to zero spawn rights
   - Expected: llm_profile_to_spawn_rights(profile) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a NET-only profile maps to zero spawn rights")
val profile = _profile(LLM_RIGHT_NET)
expect(llm_profile_to_spawn_rights(profile)).to_equal(0u32)
```

</details>

#### a PROCESS_SPAWN-only profile maps to zero spawn rights

- a PROCESS_SPAWN-only profile maps to zero spawn rights
   - Expected: llm_profile_to_spawn_rights(profile) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a PROCESS_SPAWN-only profile maps to zero spawn rights")
val profile = _profile(LLM_RIGHT_PROCESS_SPAWN)
expect(llm_profile_to_spawn_rights(profile)).to_equal(0u32)
```

</details>

#### NET and PROCESS_SPAWN stay zero even through wide-open parent and executable ceilings

- NET and PROCESS_SPAWN stay zero even through wide-open parent and executable ceilings
   - Expected: eff equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("NET and PROCESS_SPAWN stay zero even through wide-open parent and executable ceilings")
val profile = _profile(LLM_RIGHT_NET | LLM_RIGHT_PROCESS_SPAWN)
val wide_open = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC | CAP_RIGHT_MAP
val eff = llm_spawn_effective_rights(profile, wide_open, wide_open)
expect(eff).to_equal(0u32)
```

</details>

### built-in profiles: offline is narrowest, system-administration is broadest, both clamped

#### offline maps to zero spawn rights (LLM_RIGHT_NONE grants nothing)

- offline maps to zero spawn rights (LLM_RIGHT_NONE grants nothing)
   - Expected: profile_offline().rights equals `LLM_RIGHT_NONE`
   - Expected: llm_profile_to_spawn_rights(profile_offline()) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("offline maps to zero spawn rights (LLM_RIGHT_NONE grants nothing)")
expect(profile_offline().rights).to_equal(LLM_RIGHT_NONE)
expect(llm_profile_to_spawn_rights(profile_offline())).to_equal(0u32)
```

</details>

#### system-administration maps to the broadest defined spawn rights (READ|WRITE|EXEC|MAP = 71)

- system-administration maps to the broadest defined spawn rights (READ|WRITE|EXEC|MAP = 71)
   - Expected: profile_system_administration().rights equals `LLM_RIGHT_ALL`
   - Expected: llm_profile_to_spawn_rights(profile_system_administration()) equals `71u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("system-administration maps to the broadest defined spawn rights (READ|WRITE|EXEC|MAP = 71)")
expect(profile_system_administration().rights).to_equal(LLM_RIGHT_ALL)
expect(llm_profile_to_spawn_rights(profile_system_administration())).to_equal(71u32)
```

</details>

#### a narrow parent_delegable clamps system-administration down to the parent's own rights, while offline stays at zero

- a narrow parent_delegable clamps system-administration down to the parent's own rights, while offline stays at zero
- Narrow parent only delegates READ|WRITE (3); executable ceiling matches the profile's full mapped rights (71)
- offline stays at zero; system-administration is clamped down to exactly the narrow parent (3), not its own 71
   - Expected: eff_offline equals `0u32`
   - Expected: eff_sysadmin equals `3u32`
   - Expected: spawn_rights_is_subset(eff_sysadmin, parent_delegable) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a narrow parent_delegable clamps system-administration down to the parent's own rights, while offline stays at zero")
step("Narrow parent only delegates READ|WRITE (3); executable ceiling matches the profile's full mapped rights (71)")
val parent_delegable = CAP_RIGHT_READ | CAP_RIGHT_WRITE
val executable_ceiling = 71u32
val eff_offline = llm_spawn_effective_rights(profile_offline(), parent_delegable, executable_ceiling)
val eff_sysadmin = llm_spawn_effective_rights(profile_system_administration(), parent_delegable, executable_ceiling)
step("offline stays at zero; system-administration is clamped down to exactly the narrow parent (3), not its own 71")
expect(eff_offline).to_equal(0u32)
expect(eff_sysadmin).to_equal(3u32)
expect(eff_sysadmin).to_be_greater_than(eff_offline)
expect(spawn_rights_is_subset(eff_sysadmin, parent_delegable)).to_equal(true)
assert_true(llm_spawn_rights_triple_attenuated(profile_offline(), parent_delegable, executable_ceiling))
assert_true(llm_spawn_rights_triple_attenuated(profile_system_administration(), parent_delegable, executable_ceiling))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane INT-3)`
- **Design:** `doc/01_research/domain/simpleos_production_host_master_plan.md (§5.4, §17)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22e32f496d43d136ff53ee8b6213f020fecda634907d896ac6d960ff1f26f098`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22e32f496d43d136ff53ee8b6213f020fecda634907d896ac6d960ff1f26f098`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22e32f496d43d136ff53ee8b6213f020fecda634907d896ac6d960ff1f26f098`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/security/llm_profile_spawn_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/security/llm_profile_spawn_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/security/llm_profile_spawn_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'effective rights are a subset of the profile's mapped rights, parent_delegable, and executable_ceiling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the triple-attenuation oracle holds for the same fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WRITE never appears when the profile only holds FS_READ, despite wide-open parent and executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
