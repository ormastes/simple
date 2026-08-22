# Boot-Seal Readiness Specification (master plan §5.4, Phase 2)

> `_seal_ambient_spawn_on_boot()` in `src/os/kernel/boot/init_services.spl` is still GATED OFF. This gate is the evidence that arming it would be safe: it forces the SEALED behaviour locally — `spawn_authority_seal_bootstrap()` plus a non-root caller id — and asserts, per migrated userland caller, that

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot-Seal Readiness Specification (master plan §5.4, Phase 2)

`_seal_ambient_spawn_on_boot()` in `src/os/kernel/boot/init_services.spl` is still GATED OFF. This gate is the evidence that arming it would be safe: it forces the SEALED behaviour locally — `spawn_authority_seal_bootstrap()` plus a non-root caller id — and asserts, per migrated userland caller, that

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-OCAP-P2-SEAL |
| Category | Runtime / Security |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md |
| Design | doc/04_architecture/os/security/ocap_privilege_architecture.md (§P1/§P2) |
| Research | doc/01_research/os/security/llm_role_cspace_container_design.md |
| Source | `test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Boot-Seal Readiness Specification (master plan §5.4, Phase 2)

**Feature IDs:** #OS-OCAP-P2-SEAL
**Category:** Runtime / Security
**Difficulty:** 4/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md
**Design:** doc/04_architecture/os/security/ocap_privilege_architecture.md (§P1/§P2)
**Research:** doc/01_research/os/security/llm_role_cspace_container_design.md

## Overview

`_seal_ambient_spawn_on_boot()` in `src/os/kernel/boot/init_services.spl` is
still GATED OFF. This gate is the evidence that arming it would be safe: it
forces the SEALED behaviour locally — `spawn_authority_seal_bootstrap()` plus a
non-root caller id — and asserts, per migrated userland caller, that

  - the recipe path is ADMITTED (`spawn_authority_check_spawn` == 0) even though
    the same caller on the bare ambient path is DENIED (EPERM); and
  - the pouch the recipe mints is a real, PLEDGED, non-empty attenuated set with
    ZERO rejected grants — i.e. arming the seal changes nothing for that caller;
    and
  - a caller with NO recipe (`SPAWN_RECIPE_NONE`) is still denied and still gets
    the pledged deny-all set — the seal keeps its teeth.

The GLOBAL boot flag is never touched by this spec. Sealing here is local guard
state, reopened at the start of every `it` block.

## Migrated callers covered

| Recipe | Real call site |
|--------|----------------|
| `SPAWN_RECIPE_SHELL` | `src/os/apps/shell/exec.spl` :: `shell_exec_as` |
| `SPAWN_RECIPE_CONSOLE_SHELL` | `src/os/kernel/arch/riscv{32,64}/console.spl` :: launch |
| `SPAWN_RECIPE_APP_LAUNCHER` | `src/os/services/launcher/launcher_registry.spl` |

## The precondition this gate also pins

`cspace_spawn._find_source` iterates `parent.caps`, and `CapabilitySet.full()`
holds ZERO concrete tokens. So an ambient parent authorizes NOTHING under a
SpawnSpec mint. The `seeded` vs `ambient` parent cases below pin that
difference: it is the reason the arming session must install
`spawn_recipe_seed_parent_caps()` on the service tasks BEFORE flipping the flag.

## Scenarios

### boot-seal readiness: migrated callers survive the seal

#### denies a non-root ambient spawn once the window is sealed

- Verify: denies a non-root ambient spawn once the window is sealed
- force sealed behaviour with a non-root caller
   - Expected: spawn_authority_bootstrap_sealed() is true
- the bare ambient path is EPERM for the non-root caller
   - Expected: spawn_authority_check_ambient(_non_root()) equals `SPAWN_AUTHORITY_EPERM`
- and so is the recipe-aware gate when NO recipe is declared
   - Expected: spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_NONE) equals `SPAWN_AUTHORITY_EPERM`
- root itself is still admitted - boot is not broken by the seal
   - Expected: spawn_authority_check_ambient(0) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: spawn_authority_check_spawn(0, SPAWN_RECIPE_NONE) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: denies a non-root ambient spawn once the window is sealed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("force sealed behaviour with a non-root caller")
_seal_with_non_root_caller()
expect(spawn_authority_bootstrap_sealed()).to_equal(true)

step("the bare ambient path is EPERM for the non-root caller")
expect(spawn_authority_check_ambient(_non_root())).to_equal(SPAWN_AUTHORITY_EPERM)

step("and so is the recipe-aware gate when NO recipe is declared")
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_NONE)).to_equal(SPAWN_AUTHORITY_EPERM)

step("root itself is still admitted - boot is not broken by the seal")
expect(spawn_authority_check_ambient(0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(spawn_authority_check_spawn(0, SPAWN_RECIPE_NONE)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### admits the SHELL caller under its recipe while sealed

- Verify: admits the SHELL caller under its recipe while sealed
- recipe is recognised as migrated
   - Expected: spawn_recipe_is_migrated(SPAWN_RECIPE_SHELL) is true
   - Expected: spawn_recipe_name(SPAWN_RECIPE_SHELL) equals `shell`
- sealed gate ADMITS it - this is the no-op-on-arming property
   - Expected: spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_SHELL) equals `0)  # oracle: pinned constant asserted by this scenario`
- the same caller with no recipe is still denied
   - Expected: spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_NONE) equals `SPAWN_AUTHORITY_EPERM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: admits the SHELL caller under its recipe while sealed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
step("recipe is recognised as migrated")
expect(spawn_recipe_is_migrated(SPAWN_RECIPE_SHELL)).to_equal(true)
expect(spawn_recipe_name(SPAWN_RECIPE_SHELL)).to_equal("shell")

step("sealed gate ADMITS it - this is the no-op-on-arming property")
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_SHELL)).to_equal(0)  # oracle: pinned constant asserted by this scenario

step("the same caller with no recipe is still denied")
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_NONE)).to_equal(SPAWN_AUTHORITY_EPERM)
```

</details>

#### admits the CONSOLE_SHELL caller under its recipe while sealed

- Verify: admits the CONSOLE_SHELL caller under its recipe while sealed
   - Expected: spawn_recipe_is_migrated(SPAWN_RECIPE_CONSOLE_SHELL) is true
   - Expected: spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_CONSOLE_SHELL) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: spawn_recipe_name(SPAWN_RECIPE_CONSOLE_SHELL) equals `console-shell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: admits the CONSOLE_SHELL caller under its recipe while sealed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
expect(spawn_recipe_is_migrated(SPAWN_RECIPE_CONSOLE_SHELL)).to_equal(true)
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_CONSOLE_SHELL)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(spawn_recipe_name(SPAWN_RECIPE_CONSOLE_SHELL)).to_equal("console-shell")
```

</details>

#### admits the APP_LAUNCHER caller under its recipe while sealed

- Verify: admits the APP_LAUNCHER caller under its recipe while sealed
   - Expected: spawn_recipe_is_migrated(SPAWN_RECIPE_APP_LAUNCHER) is true
   - Expected: spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_APP_LAUNCHER) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: spawn_recipe_name(SPAWN_RECIPE_APP_LAUNCHER) equals `app-launcher`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: admits the APP_LAUNCHER caller under its recipe while sealed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
expect(spawn_recipe_is_migrated(SPAWN_RECIPE_APP_LAUNCHER)).to_equal(true)
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_APP_LAUNCHER)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(spawn_recipe_name(SPAWN_RECIPE_APP_LAUNCHER)).to_equal("app-launcher")
```

</details>

### boot-seal readiness: the minted pouch is real and attenuated

#### mints a non-empty PLEDGED pouch for the SHELL recipe with no rejects

- Verify: mints a non-empty PLEDGED pouch for the SHELL recipe with no rejects
- mint from the seeded parent grant
- the child pouch is PLEDGED - it can only ever shrink from here
   - Expected: caps.is_pledged is true
- it is NOT the deny-all set: every declared grant was authorized
   - Expected: caps.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_SHELL)`
   - Expected: spawn_authority_recipe_rejected_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: spawn_authority_recipe_mint_count() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: mints a non-empty PLEDGED pouch for the SHELL recipe with no rejects")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
step("mint from the seeded parent grant")
val caps = _mint_for(SPAWN_RECIPE_SHELL)

step("the child pouch is PLEDGED - it can only ever shrink from here")
expect(caps.is_pledged).to_equal(true)

step("it is NOT the deny-all set: every declared grant was authorized")
expect(caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))
expect(spawn_authority_recipe_rejected_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(spawn_authority_recipe_mint_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### mints non-empty pouches for the CONSOLE_SHELL and APP_LAUNCHER recipes

- Verify: mints non-empty pouches for the CONSOLE_SHELL and APP_LAUNCHER recipes
   - Expected: console_caps.is_pledged is true
   - Expected: console_caps.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_CONSOLE_SHELL)`
   - Expected: launcher_caps.is_pledged is true
   - Expected: launcher_caps.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_APP_LAUNCHER)`
- no grant was dropped for lack of parent authority across both
   - Expected: spawn_authority_recipe_rejected_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: spawn_authority_recipe_mint_count() equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: mints non-empty pouches for the CONSOLE_SHELL and APP_LAUNCHER recipes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
val console_caps = _mint_for(SPAWN_RECIPE_CONSOLE_SHELL)
expect(console_caps.is_pledged).to_equal(true)
expect(console_caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_CONSOLE_SHELL))

val launcher_caps = _mint_for(SPAWN_RECIPE_APP_LAUNCHER)
expect(launcher_caps.is_pledged).to_equal(true)
expect(launcher_caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_APP_LAUNCHER))

step("no grant was dropped for lack of parent authority across both")
expect(spawn_authority_recipe_rejected_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(spawn_authority_recipe_mint_count()).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### still hands the deny-all ambient set to a recipe-less sealed caller

- Verify: still hands the deny-all ambient set to a recipe-less sealed caller
- no recipe declared -> the unchanged ambient path
- pledged AND empty = the fail-closed deny-all set
   - Expected: caps.is_pledged is true
   - Expected: caps.caps.len() equals `0)  # oracle: pinned constant asserted by this scenario`
- and no recipe pouch was minted on that path
   - Expected: spawn_authority_recipe_mint_count() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: still hands the deny-all ambient set to a recipe-less sealed caller")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
step("no recipe declared -> the unchanged ambient path")
val caps = spawn_authority_spawn_caps(
    _non_root(), SPAWN_RECIPE_NONE, CapabilitySet.full())

step("pledged AND empty = the fail-closed deny-all set")
expect(caps.is_pledged).to_equal(true)
expect(caps.caps.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario

step("and no recipe pouch was minted on that path")
expect(spawn_authority_recipe_mint_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### gives root the unchanged ambient set when no recipe is declared

- Verify: gives root the unchanged ambient set when no recipe is declared
- root takes the ambient path exactly as before this module grew
   - Expected: caps.is_pledged is false
   - Expected: spawn_authority_recipe_mint_count() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: gives root the unchanged ambient set when no recipe is declared")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
step("root takes the ambient path exactly as before this module grew")
val caps = spawn_authority_spawn_caps(0, SPAWN_RECIPE_NONE, CapabilitySet.full())
expect(caps.is_pledged).to_equal(false)
expect(spawn_authority_recipe_mint_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### boot-seal readiness: the seeding precondition is load-bearing

#### mints DENY-ALL from an ambient full() parent - the arming blocker

- Verify: mints DENY-ALL from an ambient full() parent - the arming blocker
- an ambient full() parent holds ZERO concrete tokens
   - Expected: ambient_parent.caps.len() equals `0)  # oracle: pinned constant asserted by this scenario`
- so every recipe grant is REJECTED and the child is powerless
   - Expected: caps.is_pledged is true
   - Expected: caps.caps.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: mints DENY-ALL from an ambient full() parent - the arming blocker")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
step("an ambient full() parent holds ZERO concrete tokens")
val ambient_parent = CapabilitySet.full()
expect(ambient_parent.caps.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario

step("so every recipe grant is REJECTED and the child is powerless")
val caps = spawn_authority_spawn_caps(_non_root(), SPAWN_RECIPE_SHELL, ambient_parent)
expect(caps.is_pledged).to_equal(true)
expect(caps.caps.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(spawn_authority_recipe_rejected_count()).to_equal(
    spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))
```

</details>

#### mints the full recipe from a SEEDED parent - what boot must install

- Verify: mints the full recipe from a SEEDED parent - what boot must install
- the seeded root grant holds one delegable token per recipe grant
   - Expected: seeded.is_pledged is true
   - Expected: seeded.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_SHELL)`
- and every grant is then authorized - zero rejects
   - Expected: caps.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_SHELL)`
   - Expected: spawn_authority_recipe_rejected_count() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: mints the full recipe from a SEEDED parent - what boot must install")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
step("the seeded root grant holds one delegable token per recipe grant")
val seeded = spawn_recipe_seed_parent_caps(SPAWN_RECIPE_SHELL, 4242u64)
expect(seeded.is_pledged).to_equal(true)
expect(seeded.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))

step("and every grant is then authorized - zero rejects")
val caps = spawn_authority_spawn_caps(_non_root(), SPAWN_RECIPE_SHELL, seeded)
expect(caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))
expect(spawn_authority_recipe_rejected_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### boot-seal readiness: recipes request least authority

#### declares READ|EXEC and nothing else for every migrated recipe

- Verify: declares READ|EXEC and nothing else for every migrated recipe
   - Expected: spawn_recipe_rights_mask(SPAWN_RECIPE_SHELL) equals `expected`
   - Expected: spawn_recipe_rights_mask(SPAWN_RECIPE_CONSOLE_SHELL) equals `expected`
   - Expected: spawn_recipe_rights_mask(SPAWN_RECIPE_APP_LAUNCHER) equals `expected`
- no migrated recipe asks for WRITE
   - Expected: write_bit equals `0u32`
- an unmigrated recipe declares NOTHING - fail closed, not wildcard
   - Expected: spawn_recipe_rights_mask(SPAWN_RECIPE_NONE) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: declares READ|EXEC and nothing else for every migrated recipe")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val expected = CAP_RIGHT_READ | CAP_RIGHT_EXEC
expect(spawn_recipe_rights_mask(SPAWN_RECIPE_SHELL)).to_equal(expected)
expect(spawn_recipe_rights_mask(SPAWN_RECIPE_CONSOLE_SHELL)).to_equal(expected)
expect(spawn_recipe_rights_mask(SPAWN_RECIPE_APP_LAUNCHER)).to_equal(expected)

step("no migrated recipe asks for WRITE")
val write_bit = spawn_recipe_rights_mask(SPAWN_RECIPE_SHELL) & CAP_RIGHT_WRITE
expect(write_bit).to_equal(0u32)

step("an unmigrated recipe declares NOTHING - fail closed, not wildcard")
expect(spawn_recipe_rights_mask(SPAWN_RECIPE_NONE)).to_equal(0u32)
```

</details>

#### pins each recipe to its narrow path prefix

- Verify: pins each recipe to its narrow path prefix
   - Expected: spawn_recipe_exec_prefix(SPAWN_RECIPE_SHELL) equals `/bin/`
   - Expected: spawn_recipe_read_prefix(SPAWN_RECIPE_SHELL) equals `/bin/`
   - Expected: spawn_recipe_exec_prefix(SPAWN_RECIPE_APP_LAUNCHER) equals `/sys/apps/`
   - Expected: spawn_recipe_read_prefix(SPAWN_RECIPE_APP_LAUNCHER) equals `/sys/apps/`
   - Expected: spawn_recipe_exec_prefix(SPAWN_RECIPE_NONE) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: pins each recipe to its narrow path prefix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(spawn_recipe_exec_prefix(SPAWN_RECIPE_SHELL)).to_equal("/bin/")
expect(spawn_recipe_read_prefix(SPAWN_RECIPE_SHELL)).to_equal("/bin/")
expect(spawn_recipe_exec_prefix(SPAWN_RECIPE_APP_LAUNCHER)).to_equal("/sys/apps/")
expect(spawn_recipe_read_prefix(SPAWN_RECIPE_APP_LAUNCHER)).to_equal("/sys/apps/")
expect(spawn_recipe_exec_prefix(SPAWN_RECIPE_NONE)).to_equal("")
```

</details>

#### meets the profile attenuation deny-wins at the recipe

- Verify: meets the profile attenuation deny-wins at the recipe
- no profile: the child gets the recipe declaration, not the parent's WRITE
   - Expected: no_profile equals `CAP_RIGHT_READ | CAP_RIGHT_EXEC`
   - Expected: spawn_rights_is_subset(no_profile, parent) is true
- a profile can only REMOVE - never add back the parent's WRITE
   - Expected: with_profile equals `CAP_RIGHT_READ`
   - Expected: spawn_rights_is_subset(with_profile, no_profile) is true
- an unmigrated recipe meets to zero, whatever the parent holds


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: meets the profile attenuation deny-wins at the recipe")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
step("no profile: the child gets the recipe declaration, not the parent's WRITE")
val no_profile = spawn_recipe_effective_rights(
    SPAWN_RECIPE_SHELL, parent, SPAWN_PROFILE_MASK_ALL)
expect(no_profile).to_equal(CAP_RIGHT_READ | CAP_RIGHT_EXEC)
expect(spawn_rights_is_subset(no_profile, parent)).to_equal(true)

step("a profile can only REMOVE - never add back the parent's WRITE")
val with_profile = spawn_recipe_effective_rights(
    SPAWN_RECIPE_SHELL, parent, CAP_RIGHT_READ)
expect(with_profile).to_equal(CAP_RIGHT_READ)
expect(spawn_rights_is_subset(with_profile, no_profile)).to_equal(true)

step("an unmigrated recipe meets to zero, whatever the parent holds")
expect(spawn_recipe_effective_rights(
    SPAWN_RECIPE_NONE, parent, SPAWN_PROFILE_MASK_ALL)).to_equal(0u32)
```

</details>

### boot-seal readiness: recipe propagation is scoped, not sticky

#### clears the declared recipe so it cannot admit a later ambient spawn

- Verify: clears the declared recipe so it cannot admit a later ambient spawn
- declare a recipe the way a migrated call site does
   - Expected: spawn_authority_current_recipe() equals `SPAWN_RECIPE_APP_LAUNCHER`
- clearing it returns the caller to the sealed ambient verdict
   - Expected: spawn_authority_current_recipe() equals `SPAWN_RECIPE_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_SPAWN_SEAL_READINESS-001
step("Verify: clears the declared recipe so it cannot admit a later ambient spawn")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_seal_with_non_root_caller()
step("declare a recipe the way a migrated call site does")
spawn_authority_note_recipe(SPAWN_RECIPE_APP_LAUNCHER)
expect(spawn_authority_current_recipe()).to_equal(SPAWN_RECIPE_APP_LAUNCHER)
expect(spawn_authority_check_spawn(
    _non_root(), spawn_authority_current_recipe())).to_equal(0)  # oracle: pinned constant asserted by this scenario

step("clearing it returns the caller to the sealed ambient verdict")
spawn_authority_clear_recipe()
expect(spawn_authority_current_recipe()).to_equal(SPAWN_RECIPE_NONE)
expect(spawn_authority_check_spawn(
    _non_root(), spawn_authority_current_recipe())).to_equal(SPAWN_AUTHORITY_EPERM)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`
- **Design:** `doc/04_architecture/os/security/ocap_privilege_architecture.md (§P1/§P2)`
- **Research:** `doc/01_research/os/security/llm_role_cspace_container_design.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d60923d15a3e249591335bc06eca08a64a71d400b4958f9e04c020b294a389f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d60923d15a3e249591335bc06eca08a64a71d400b4958f9e04c020b294a389f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d60923d15a3e249591335bc06eca08a64a71d400b4958f9e04c020b294a389f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/spawn_seal_readiness_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/spawn_seal_readiness_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/loader/spawn_seal_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/spawn_seal_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
