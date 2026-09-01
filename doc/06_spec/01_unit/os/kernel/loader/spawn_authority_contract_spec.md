# Spawn Authority Contract Specification (P2 Process/Loader)

> Master plan §5.4 "Remove ambient spawn authority": `spawn_full()` is legal only for the root task during bootstrap. This spec is the loader-side contract for `src/os/kernel/loader/spawn_authority.spl`:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spawn Authority Contract Specification (P2 Process/Loader)

Master plan §5.4 "Remove ambient spawn authority": `spawn_full()` is legal only for the root task during bootstrap. This spec is the loader-side contract for `src/os/kernel/loader/spawn_authority.spl`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-P2-SPAWN-AUTH |
| Category | Runtime / Security |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane P2) |
| Design | doc/01_research/domain/simpleos_production_host_master_plan.md (§5.4) |
| Research | doc/01_research/domain/simpleos_production_host_master_plan.md |
| Source | `test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Master plan §5.4 "Remove ambient spawn authority": `spawn_full()` is legal only
for the root task during bootstrap. This spec is the loader-side contract for
`src/os/kernel/loader/spawn_authority.spl`:

  - while the bootstrap window is OPEN, ambient spawn is allowed (boot must keep
    working) and yields the full ambient set;
  - after `spawn_authority_seal_bootstrap()`, only the root task keeps ambient
    authority; every other caller is denied EPERM and receives the PLEDGED
    deny-all set, never a god-mode one (fail closed);
  - rights derived from a SpawnSpec are an INTERSECTION of parent, executable
    ceiling, system ceiling and manifest request, minus explicit denials — so a
    child's rights are always a SUBSET of the parent's (no amplification via
    child creation).

State lives in scalar module vars inside the guard (freestanding discipline: no
module-level array initializers, no classes, no trait objects on the ring-0
path), so every assertion goes through an accessor fn.

## Scenarios

### spawn authority contract (master plan 5.4)

#### allows ambient spawn while the bootstrap window is open

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### keeps ambient spawn for the root task after bootstrap is sealed

- seal the bootstrap window
   - Expected: spawn_authority_bootstrap_sealed() is true
   - Expected: spawn_authority_root_task() equals `0`
   - Expected: spawn_authority_is_root(0) is true
- root still takes the ambient path
   - Expected: spawn_authority_check_ambient(0) equals `0`
   - Expected: caps.is_pledged is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spawn_authority_reopen_bootstrap()
spawn_authority_set_root_task(0)
step("seal the bootstrap window")
spawn_authority_seal_bootstrap()
expect(spawn_authority_bootstrap_sealed()).to_equal(true)
expect(spawn_authority_root_task()).to_equal(0)
expect(spawn_authority_is_root(0)).to_equal(true)

step("root still takes the ambient path")
expect(spawn_authority_check_ambient(0)).to_equal(0)
val caps = spawn_authority_ambient_caps(0)
expect(caps.is_pledged).to_equal(false)
```

</details>

#### denies post-bootstrap ambient spawn for a non-root caller

- a non-root caller is refused with EPERM
   - Expected: spawn_authority_is_root(7) is false
   - Expected: spawn_authority_check_ambient(7) equals `SPAWN_AUTHORITY_EPERM`
- and receives the PLEDGED deny-all set, not god mode
   - Expected: caps.is_pledged is true
   - Expected: caps.caps.len().to_i64() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spawn_authority_reopen_bootstrap()
spawn_authority_set_root_task(0)
spawn_authority_seal_bootstrap()

step("a non-root caller is refused with EPERM")
expect(spawn_authority_is_root(7)).to_equal(false)
expect(spawn_authority_check_ambient(7)).to_equal(SPAWN_AUTHORITY_EPERM)

step("and receives the PLEDGED deny-all set, not god mode")
val caps = spawn_authority_ambient_caps(7)
expect(caps.is_pledged).to_equal(true)
expect(caps.caps.len().to_i64()).to_equal(0)
```

</details>

#### follows the declared root task when root is not the kernel sentinel

- task 1 is root, task 0 is now an ordinary caller
   - Expected: spawn_authority_check_ambient(1) equals `0`
   - Expected: spawn_authority_check_ambient(0) equals `SPAWN_AUTHORITY_EPERM`
- restore the kernel-origin sentinel for later examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spawn_authority_reopen_bootstrap()
spawn_authority_set_root_task(1)
spawn_authority_seal_bootstrap()
step("task 1 is root, task 0 is now an ordinary caller")
expect(spawn_authority_check_ambient(1)).to_equal(0)
expect(spawn_authority_check_ambient(0)).to_equal(SPAWN_AUTHORITY_EPERM)
step("restore the kernel-origin sentinel for later examples")
spawn_authority_set_root_task(0)
```

</details>

#### propagates the recorded caller through the cross-arch bridge scalar

- the loader records the caller before descending into the bridge
   - Expected: spawn_authority_current_caller() equals `0`
   - Expected: spawn_authority_current_caller() equals `99`
- and clears it afterwards so boot paths read the root sentinel
   - Expected: spawn_authority_current_caller() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("the loader records the caller before descending into the bridge")
spawn_authority_clear_caller()
expect(spawn_authority_current_caller()).to_equal(0)
spawn_authority_note_caller(99)
expect(spawn_authority_current_caller()).to_equal(99)
step("and clears it afterwards so boot paths read the root sentinel")
spawn_authority_clear_caller()
expect(spawn_authority_current_caller()).to_equal(0)
```

</details>

### effective rights are an intersection (no amplification)

#### intersects parent, executable ceiling, system ceiling and request

- parent holds read+write+exec
- executable ceiling drops exec, request asks for read+write
   - Expected: eff equals `CAP_RIGHT_READ | CAP_RIGHT_WRITE`
   - Expected: spawn_rights_is_subset(eff, parent) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parent holds read+write+exec")
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
step("executable ceiling drops exec, request asks for read+write")
val eff = spawn_effective_rights(
    parent,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE,
    0u32
)
expect(eff).to_equal(CAP_RIGHT_READ | CAP_RIGHT_WRITE)
expect(spawn_rights_is_subset(eff, parent)).to_equal(true)
```

</details>

#### never grants a right the parent lacks (request cannot widen)

- parent holds read only, request asks for read+write+admin
   - Expected: eff equals `CAP_RIGHT_READ`
   - Expected: spawn_rights_is_subset(eff, parent) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parent holds read only, request asks for read+write+admin")
val parent = CAP_RIGHT_READ
val eff = spawn_effective_rights(
    parent,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_ADMIN,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_ADMIN,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_ADMIN,
    0u32
)
expect(eff).to_equal(CAP_RIGHT_READ)
expect(spawn_rights_is_subset(eff, parent)).to_equal(true)
```

</details>

#### subtracts explicit denials last (deny wins)

- write is explicitly denied even though every ceiling allows it
   - Expected: eff equals `CAP_RIGHT_READ`
- spawn_rights_without clears only the denied bits
   - Expected: spawn_rights_without(parent, CAP_RIGHT_WRITE) equals `CAP_RIGHT_READ`
   - Expected: spawn_rights_without(parent, CAP_RIGHT_ADMIN) equals `parent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE
step("write is explicitly denied even though every ceiling allows it")
val eff = spawn_effective_rights(parent, parent, parent, parent, CAP_RIGHT_WRITE)
expect(eff).to_equal(CAP_RIGHT_READ)
step("spawn_rights_without clears only the denied bits")
expect(spawn_rights_without(parent, CAP_RIGHT_WRITE)).to_equal(CAP_RIGHT_READ)
expect(spawn_rights_without(parent, CAP_RIGHT_ADMIN)).to_equal(parent)
```

</details>

#### bounds SpawnSpec-requested rights by the parent

- a grant asking for admin gets nothing extra - masked by parent
   - Expected: spawn_spec_requested_rights(spec, parent) equals `0u32`
- a zero rights_mask means inherit the parent - not all rights
   - Expected: spawn_spec_requested_rights(inherit, parent) equals `parent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE
step("a grant asking for admin gets nothing extra - masked by parent")
val spec = _spec_with([_grant("svc.admin", CAP_RIGHT_ADMIN)])
expect(spawn_spec_requested_rights(spec, parent)).to_equal(0u32)
step("a zero rights_mask means inherit the parent - not all rights")
val inherit = _spec_with([_grant_identity("svc.inherit")])
expect(spawn_spec_requested_rights(inherit, parent)).to_equal(parent)
```

</details>

#### derives SpawnSpec rights as a subset of the parent

- union of grants, intersected with both ceilings, minus denials
   - Expected: eff equals `CAP_RIGHT_READ`
   - Expected: spawn_rights_is_subset(eff, parent) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
val spec = _spec_with([
    _grant("svc.files", CAP_RIGHT_READ | CAP_RIGHT_WRITE),
    _grant("svc.admin", CAP_RIGHT_ADMIN)
])
step("union of grants, intersected with both ceilings, minus denials")
val eff = spawn_spec_effective_rights(
    spec,
    parent,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC,
    CAP_RIGHT_READ | CAP_RIGHT_WRITE,
    CAP_RIGHT_WRITE
)
expect(eff).to_equal(CAP_RIGHT_READ)
expect(spawn_rights_is_subset(eff, parent)).to_equal(true)
```

</details>

#### yields an empty right set for an empty recipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE
val empty_spec = _spec_with([])
expect(spawn_spec_requested_rights(empty_spec, parent)).to_equal(0u32)
expect(spawn_spec_effective_rights(empty_spec, parent, parent, parent, 0u32)).to_equal(0u32)
```

</details>

### profile meet point (P8 x P2 hand-off: attenuation and spawn rights meet at spawn time)

#### meets all three inputs - result is a subset of parent, request and profile

- parent read+write+exec, request read+write, profile read+exec
- only read survives all three - absolute value, not just subset
   - Expected: eff equals `CAP_RIGHT_READ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parent read+write+exec, request read+write, profile read+exec")
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
val requested = CAP_RIGHT_READ | CAP_RIGHT_WRITE
val profile = CAP_RIGHT_READ | CAP_RIGHT_EXEC
val eff = spawn_effective_rights_with_profile(parent, requested, profile)
step("only read survives all three - absolute value, not just subset")
expect(eff).to_equal(CAP_RIGHT_READ)
assert_true(spawn_rights_is_subset(eff, parent))
assert_true(spawn_rights_is_subset(eff, requested))
assert_true(spawn_rights_is_subset(eff, profile))
```

</details>

#### keeps the no-profile path identical - SPAWN_PROFILE_MASK_ALL is the meet identity

- with the all-rights mask the meet equals the plain intersection
   - Expected: spawn_effective_rights_with_profile(parent, requested, SPAWN_PROFILE_MASK_ALL) equals `parent & requested`
- and the SpawnSpec decision point is bit-for-bit unchanged
   - Expected: with_all equals `base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
val requested = CAP_RIGHT_READ | CAP_RIGHT_WRITE
step("with the all-rights mask the meet equals the plain intersection")
expect(spawn_effective_rights_with_profile(parent, requested, SPAWN_PROFILE_MASK_ALL)).to_equal(parent & requested)
step("and the SpawnSpec decision point is bit-for-bit unchanged")
val spec = _spec_with([
    _grant("svc.files", CAP_RIGHT_READ | CAP_RIGHT_WRITE),
    _grant("svc.admin", CAP_RIGHT_ADMIN)
])
val base = spawn_spec_effective_rights(
    spec, parent, parent, CAP_RIGHT_READ | CAP_RIGHT_WRITE, CAP_RIGHT_WRITE)
val with_all = spawn_spec_effective_rights_with_profile(
    spec, parent, parent, CAP_RIGHT_READ | CAP_RIGHT_WRITE, CAP_RIGHT_WRITE,
    SPAWN_PROFILE_MASK_ALL)
expect(with_all).to_equal(base)
```

</details>

#### never lets a profile ADD a right the parent lacks

- parent holds read only - profile claims write+admin as well
   - Expected: eff equals `CAP_RIGHT_READ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parent holds read only - profile claims write+admin as well")
val parent = CAP_RIGHT_READ
val requested = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_ADMIN
val profile = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_ADMIN
val eff = spawn_effective_rights_with_profile(parent, requested, profile)
expect(eff).to_equal(CAP_RIGHT_READ)
assert_true(spawn_rights_is_subset(eff, parent))
```

</details>

#### yields 0 for an all-deny profile mask (deny wins absolutely)

- a zero profile mask annihilates every right - even root-ish parents
   - Expected: spawn_effective_rights_with_profile(parent, parent, 0u32) equals `0u32`
   - Expected: spawn_spec_effective_rights_with_profile(spec, parent, parent, parent, 0u32, 0u32) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
step("a zero profile mask annihilates every right - even root-ish parents")
expect(spawn_effective_rights_with_profile(parent, parent, 0u32)).to_equal(0u32)
val spec = _spec_with([_grant_identity("svc.inherit")])
expect(spawn_spec_effective_rights_with_profile(spec, parent, parent, parent, 0u32, 0u32)).to_equal(0u32)
```

</details>

#### meets the SpawnSpec formula with a partial profile mask at the decision point

- base formula grants read+write; profile mask keeps read only
   - Expected: eff equals `CAP_RIGHT_READ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
val spec = _spec_with([_grant("svc.files", CAP_RIGHT_READ | CAP_RIGHT_WRITE)])
step("base formula grants read+write; profile mask keeps read only")
val eff = spawn_spec_effective_rights_with_profile(
    spec, parent, parent, parent, 0u32, CAP_RIGHT_READ)
expect(eff).to_equal(CAP_RIGHT_READ)
assert_true(spawn_rights_is_subset(eff, parent))
assert_true(spawn_rights_is_subset(eff, CAP_RIGHT_READ))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane P2)`
- **Design:** `doc/01_research/domain/simpleos_production_host_master_plan.md (§5.4)`
- **Research:** `doc/01_research/domain/simpleos_production_host_master_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5873766f9a639ecc801d9f4e322926129e0a970d291024cdb8c1dff3c527503`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5873766f9a639ecc801d9f4e322926129e0a970d291024cdb8c1dff3c527503`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5873766f9a639ecc801d9f4e322926129e0a970d291024cdb8c1dff3c527503`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/spawn_authority_contract_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/spawn_authority_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/spawn_authority_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl:71:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'allows ambient spawn while the bootstrap window is open' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps ambient spawn for the root task after bootstrap is sealed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies post-bootstrap ambient spawn for a non-root caller' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'follows the declared root task when root is not the kernel sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl:199:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'yields an empty right set for an empty recipe' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
