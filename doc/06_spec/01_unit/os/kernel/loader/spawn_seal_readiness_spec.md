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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### admits the SHELL caller under its recipe while sealed

- recipe is recognised as migrated
   - Expected: spawn_recipe_is_migrated(SPAWN_RECIPE_SHELL) is true
   - Expected: spawn_recipe_name(SPAWN_RECIPE_SHELL) equals `shell`
- sealed gate ADMITS it - this is the no-op-on-arming property
   - Expected: spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_SHELL) equals `0`
- the same caller with no recipe is still denied
   - Expected: spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_NONE) equals `SPAWN_AUTHORITY_EPERM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
step("recipe is recognised as migrated")
expect(spawn_recipe_is_migrated(SPAWN_RECIPE_SHELL)).to_equal(true)
expect(spawn_recipe_name(SPAWN_RECIPE_SHELL)).to_equal("shell")

step("sealed gate ADMITS it - this is the no-op-on-arming property")
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_SHELL)).to_equal(0)

step("the same caller with no recipe is still denied")
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_NONE)).to_equal(SPAWN_AUTHORITY_EPERM)
```

</details>

#### admits the CONSOLE_SHELL caller under its recipe while sealed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
expect(spawn_recipe_is_migrated(SPAWN_RECIPE_CONSOLE_SHELL)).to_equal(true)
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_CONSOLE_SHELL)).to_equal(0)
expect(spawn_recipe_name(SPAWN_RECIPE_CONSOLE_SHELL)).to_equal("console-shell")
```

</details>

#### admits the APP_LAUNCHER caller under its recipe while sealed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
expect(spawn_recipe_is_migrated(SPAWN_RECIPE_APP_LAUNCHER)).to_equal(true)
expect(spawn_authority_check_spawn(_non_root(), SPAWN_RECIPE_APP_LAUNCHER)).to_equal(0)
expect(spawn_recipe_name(SPAWN_RECIPE_APP_LAUNCHER)).to_equal("app-launcher")
```

</details>

### boot-seal readiness: the minted pouch is real and attenuated

#### mints a non-empty PLEDGED pouch for the SHELL recipe with no rejects

- mint from the seeded parent grant
- the child pouch is PLEDGED - it can only ever shrink from here
   - Expected: caps.is_pledged is true
- it is NOT the deny-all set: every declared grant was authorized
   - Expected: caps.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_SHELL)`
   - Expected: spawn_authority_recipe_rejected_count() equals `0`
   - Expected: spawn_authority_recipe_mint_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
step("mint from the seeded parent grant")
val caps = _mint_for(SPAWN_RECIPE_SHELL)

step("the child pouch is PLEDGED - it can only ever shrink from here")
expect(caps.is_pledged).to_equal(true)

step("it is NOT the deny-all set: every declared grant was authorized")
expect(caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))
expect(spawn_authority_recipe_rejected_count()).to_equal(0)
expect(spawn_authority_recipe_mint_count()).to_equal(1)
```

</details>

#### mints non-empty pouches for the CONSOLE_SHELL and APP_LAUNCHER recipes

- no grant was dropped for lack of parent authority across both
   - Expected: spawn_authority_recipe_rejected_count() equals `0`
   - Expected: spawn_authority_recipe_mint_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
val console_caps = _mint_for(SPAWN_RECIPE_CONSOLE_SHELL)
expect(console_caps.is_pledged).to_equal(true)
expect(console_caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_CONSOLE_SHELL))

val launcher_caps = _mint_for(SPAWN_RECIPE_APP_LAUNCHER)
expect(launcher_caps.is_pledged).to_equal(true)
expect(launcher_caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_APP_LAUNCHER))

step("no grant was dropped for lack of parent authority across both")
expect(spawn_authority_recipe_rejected_count()).to_equal(0)
expect(spawn_authority_recipe_mint_count()).to_equal(2)
```

</details>

#### still hands the deny-all ambient set to a recipe-less sealed caller

- no recipe declared -> the unchanged ambient path
- pledged AND empty = the fail-closed deny-all set
   - Expected: caps.is_pledged is true
   - Expected: caps.caps.len() equals `0`
- and no recipe pouch was minted on that path
   - Expected: spawn_authority_recipe_mint_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
step("no recipe declared -> the unchanged ambient path")
val caps = spawn_authority_spawn_caps(
    _non_root(), SPAWN_RECIPE_NONE, CapabilitySet.full())

step("pledged AND empty = the fail-closed deny-all set")
expect(caps.is_pledged).to_equal(true)
expect(caps.caps.len()).to_equal(0)

step("and no recipe pouch was minted on that path")
expect(spawn_authority_recipe_mint_count()).to_equal(0)
```

</details>

#### gives root the unchanged ambient set when no recipe is declared

- root takes the ambient path exactly as before this module grew
   - Expected: caps.is_pledged is false
   - Expected: spawn_authority_recipe_mint_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
step("root takes the ambient path exactly as before this module grew")
val caps = spawn_authority_spawn_caps(0, SPAWN_RECIPE_NONE, CapabilitySet.full())
expect(caps.is_pledged).to_equal(false)
expect(spawn_authority_recipe_mint_count()).to_equal(0)
```

</details>

### boot-seal readiness: the seeding precondition is load-bearing

#### mints DENY-ALL from an ambient full() parent - the arming blocker

- an ambient full() parent holds ZERO concrete tokens
   - Expected: ambient_parent.caps.len() equals `0`
- so every recipe grant is REJECTED and the child is powerless
   - Expected: caps.is_pledged is true
   - Expected: caps.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
step("an ambient full() parent holds ZERO concrete tokens")
val ambient_parent = CapabilitySet.full()
expect(ambient_parent.caps.len()).to_equal(0)

step("so every recipe grant is REJECTED and the child is powerless")
val caps = spawn_authority_spawn_caps(_non_root(), SPAWN_RECIPE_SHELL, ambient_parent)
expect(caps.is_pledged).to_equal(true)
expect(caps.caps.len()).to_equal(0)
expect(spawn_authority_recipe_rejected_count()).to_equal(
    spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))
```

</details>

#### mints the full recipe from a SEEDED parent - what boot must install

- the seeded root grant holds one delegable token per recipe grant
   - Expected: seeded.is_pledged is true
   - Expected: seeded.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_SHELL)`
- and every grant is then authorized - zero rejects
   - Expected: caps.caps.len() equals `spawn_recipe_grant_count(SPAWN_RECIPE_SHELL)`
   - Expected: spawn_authority_recipe_rejected_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
step("the seeded root grant holds one delegable token per recipe grant")
val seeded = spawn_recipe_seed_parent_caps(SPAWN_RECIPE_SHELL, 4242u64)
expect(seeded.is_pledged).to_equal(true)
expect(seeded.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))

step("and every grant is then authorized - zero rejects")
val caps = spawn_authority_spawn_caps(_non_root(), SPAWN_RECIPE_SHELL, seeded)
expect(caps.caps.len()).to_equal(spawn_recipe_grant_count(SPAWN_RECIPE_SHELL))
expect(spawn_authority_recipe_rejected_count()).to_equal(0)
```

</details>

### boot-seal readiness: recipes request least authority

#### declares READ|EXEC and nothing else for every migrated recipe

- no migrated recipe asks for WRITE
   - Expected: write_bit equals `0u32`
- an unmigrated recipe declares NOTHING - fail closed, not wildcard
   - Expected: spawn_recipe_rights_mask(SPAWN_RECIPE_NONE) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(spawn_recipe_exec_prefix(SPAWN_RECIPE_SHELL)).to_equal("/bin/")
expect(spawn_recipe_read_prefix(SPAWN_RECIPE_SHELL)).to_equal("/bin/")
expect(spawn_recipe_exec_prefix(SPAWN_RECIPE_APP_LAUNCHER)).to_equal("/sys/apps/")
expect(spawn_recipe_read_prefix(SPAWN_RECIPE_APP_LAUNCHER)).to_equal("/sys/apps/")
expect(spawn_recipe_exec_prefix(SPAWN_RECIPE_NONE)).to_equal("")
```

</details>

#### meets the profile attenuation deny-wins at the recipe

- no profile: the child gets the recipe declaration, not the parent's WRITE
   - Expected: no_profile equals `CAP_RIGHT_READ | CAP_RIGHT_EXEC`
   - Expected: spawn_rights_is_subset(no_profile, parent) is true
- a profile can only REMOVE - never add back the parent's WRITE
   - Expected: with_profile equals `CAP_RIGHT_READ`
   - Expected: spawn_rights_is_subset(with_profile, no_profile) is true
- an unmigrated recipe meets to zero, whatever the parent holds


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- declare a recipe the way a migrated call site does
   - Expected: spawn_authority_current_recipe() equals `SPAWN_RECIPE_APP_LAUNCHER`
- clearing it returns the caller to the sealed ambient verdict
   - Expected: spawn_authority_current_recipe() equals `SPAWN_RECIPE_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seal_with_non_root_caller()
step("declare a recipe the way a migrated call site does")
spawn_authority_note_recipe(SPAWN_RECIPE_APP_LAUNCHER)
expect(spawn_authority_current_recipe()).to_equal(SPAWN_RECIPE_APP_LAUNCHER)
expect(spawn_authority_check_spawn(
    _non_root(), spawn_authority_current_recipe())).to_equal(0)

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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `03f1e294540c2df8b94b6b9a4e60ab9c043482e0a4b7bc63936bff8831283f18`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03f1e294540c2df8b94b6b9a4e60ab9c043482e0a4b7bc63936bff8831283f18`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03f1e294540c2df8b94b6b9a4e60ab9c043482e0a4b7bc63936bff8831283f18`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **79/100**; blockers: **0**.

SSpec documentization score: 79/100
source: test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/spawn_seal_readiness_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/spawn_seal_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/spawn_seal_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:104:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'denies a non-root ambient spawn once the window is sealed' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits the SHELL caller under its recipe while sealed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:133:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'admits the CONSOLE_SHELL caller under its recipe while sealed' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:139:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'admits the APP_LAUNCHER caller under its recipe while sealed' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mints a non-empty PLEDGED pouch for the SHELL recipe with no rejects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mints non-empty pouches for the CONSOLE_SHELL and APP_LAUNCHER recipes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl:236:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'pins each recipe to its narrow path prefix' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
