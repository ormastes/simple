# Spawn Authority ENFORCEMENT Wiring Specification

> The spawn-authority guard (`src/os/kernel/loader/spawn_authority.spl`) already had a proven contract, but it was UNARMED: nothing sealed the bootstrap window and the three ambient `spawn_full()` sites in `syscall_process.spl` bypassed it entirely. A guard nobody calls denies nothing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spawn Authority ENFORCEMENT Wiring Specification

The spawn-authority guard (`src/os/kernel/loader/spawn_authority.spl`) already had a proven contract, but it was UNARMED: nothing sealed the bootstrap window and the three ambient `spawn_full()` sites in `syscall_process.spl` bypassed it entirely. A guard nobody calls denies nothing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-P2-SPAWN-AUTH-ENFORCE |
| Category | Runtime / Security |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane INT-1) |
| Design | doc/01_research/domain/simpleos_production_host_master_plan.md (5.4) |
| Research | doc/01_research/domain/simpleos_production_host_master_plan.md |
| Source | `test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The spawn-authority guard (`src/os/kernel/loader/spawn_authority.spl`) already
had a proven contract, but it was UNARMED: nothing sealed the bootstrap window
and the three ambient `spawn_full()` sites in `syscall_process.spl` bypassed it
entirely. A guard nobody calls denies nothing.

This spec is the enforcement half. It proves two things:

  - the enforcement STATE MACHINE, exercised through the guard's public API
    directly (no kernel boot required): open window admits everyone, sealing
    admits only the declared root task, reopening admits everyone again, and
    every refusal is counted so a gate can observe it;
  - the WIRING, i.e. that each of the three ambient spawn sites actually asks the
    guard before handing out authority, and that the boot path's seal call is
    placed last -- but NOT that boot arms it. It does not: the seal call sits
    behind `_seal_ambient_spawn_on_boot()`, which returns false. The gate's OFF
    state is asserted here on purpose (see `doc/03_plan/infra/agent_sessions/
    dict_values.md`, "Seal gate status 2026-08-01") so that flipping it without
    the accompanying evidence run turns this spec RED instead of passing silently.

Guard state lives in scalar module vars (freestanding discipline: no
module-level array initializers, no classes, no trait-object dispatch on the
ring-0 path), and module vars mutated inside fns are not readable from an `it`
block, so every state assertion goes through an accessor fn.

## Scenarios

### spawn authority enforcement wiring (master plan 5.4)

#### admits every caller while the bootstrap window is open

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### denies a non-root caller once the bootstrap window is sealed

- arm the guard exactly as init_all_services does at end of boot
- the root task keeps ambient authority
   - Expected: spawn_authority_check_ambient(ROOT_CALLER) equals `0`
- every other caller is refused EPERM and gets the deny-all set
   - Expected: spawn_authority_check_ambient(USER_CALLER) equals `-1`
   - Expected: spawn_authority_check_ambient(USER_CALLER) equals `SPAWN_AUTHORITY_EPERM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("arm the guard exactly as init_all_services does at end of boot")
spawn_authority_reopen_bootstrap()
spawn_authority_set_root_task(ROOT_CALLER)
spawn_authority_seal_bootstrap()
assert_true(spawn_authority_bootstrap_sealed())

step("the root task keeps ambient authority")
assert_true(spawn_authority_is_root(ROOT_CALLER))
expect(spawn_authority_check_ambient(ROOT_CALLER)).to_equal(0)
val root_caps = spawn_authority_ambient_caps(ROOT_CALLER)
assert_false(root_caps.is_pledged)

step("every other caller is refused EPERM and gets the deny-all set")
assert_false(spawn_authority_is_root(USER_CALLER))
expect(spawn_authority_check_ambient(USER_CALLER)).to_equal(-1)
expect(spawn_authority_check_ambient(USER_CALLER)).to_equal(SPAWN_AUTHORITY_EPERM)
val denied_caps = spawn_authority_ambient_caps(USER_CALLER)
assert_true(denied_caps.is_pledged)
```

</details>

#### counts each refused ambient spawn so a gate can observe it

- seal the window with task 0 as root
- an allowed ambient grant does not move the denial counter
   - Expected: spawn_authority_denial_count() - before_allowed equals `0`
- each refused ambient grant increments the counter by exactly one
   - Expected: spawn_authority_denial_count() - before_denied equals `1`
   - Expected: spawn_authority_denial_count() - before_denied equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("seal the window with task 0 as root")
spawn_authority_reopen_bootstrap()
spawn_authority_set_root_task(ROOT_CALLER)
spawn_authority_seal_bootstrap()

step("an allowed ambient grant does not move the denial counter")
val before_allowed = spawn_authority_denial_count()
val allowed = spawn_authority_ambient_caps(ROOT_CALLER)
assert_false(allowed.is_pledged)
expect(spawn_authority_denial_count() - before_allowed).to_equal(0)

step("each refused ambient grant increments the counter by exactly one")
val before_denied = spawn_authority_denial_count()
val refused = spawn_authority_ambient_caps(USER_CALLER)
assert_true(refused.is_pledged)
expect(spawn_authority_denial_count() - before_denied).to_equal(1)
val refused_again = spawn_authority_ambient_caps(USER_CALLER)
assert_true(refused_again.is_pledged)
expect(spawn_authority_denial_count() - before_denied).to_equal(2)
```

</details>

#### readmits every caller when the bootstrap window is reopened

- seal, then reopen the window (boot-phase restart / harness reset)
   - Expected: spawn_authority_check_ambient(USER_CALLER) equals `-1`
- the previously denied caller passes again and the count is frozen
   - Expected: spawn_authority_check_ambient(USER_CALLER) equals `0`
   - Expected: spawn_authority_denial_count() - frozen equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("seal, then reopen the window (boot-phase restart / harness reset)")
spawn_authority_set_root_task(ROOT_CALLER)
spawn_authority_seal_bootstrap()
expect(spawn_authority_check_ambient(USER_CALLER)).to_equal(-1)
spawn_authority_reopen_bootstrap()

step("the previously denied caller passes again and the count is frozen")
val frozen = spawn_authority_denial_count()
assert_false(spawn_authority_bootstrap_sealed())
expect(spawn_authority_check_ambient(USER_CALLER)).to_equal(0)
val reopened_caps = spawn_authority_ambient_caps(USER_CALLER)
assert_false(reopened_caps.is_pledged)
expect(spawn_authority_denial_count() - frozen).to_equal(0)
```

</details>

#### routes all three ambient spawn sites in syscall_process through the guard

- the syscall module imports the guard, not the raw ambient grant
- no ambient spawn site still calls spawn_full() directly
   - Expected: direct_grant equals `-1`
- all three sites take their caps from the guard
   - Expected: guarded_caps.len() equals `4`
- all three sites ask the guard before spawning
   - Expected: checks.len() equals `4`
- a refused caller gets a permission-denied result, never a task
- the caller id comes from the scheduler, never a fabricated value


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("the syscall module imports the guard, not the raw ambient grant")
val syscalls = file_read(SYSCALL_PROCESS_PATH)
expect(syscalls).to_contain("use os.kernel.loader.spawn_authority.")
# STALE ASSERTION FIXED 2026-08-01: `spawn_authority_check_ambient` is no
# longer named in syscall_process -- the recipe half of master plan 5.4
# replaced it with `spawn_authority_check_spawn(caller, recipe)`, which
# falls through to the ambient check when no recipe is declared. The old
# literal matched nothing and this case was RED at HEAD.
expect(syscalls).to_contain("spawn_authority_check_spawn")
expect(syscalls).to_contain("spawn_authority_ambient_caps")

step("no ambient spawn site still calls spawn_full() directly")
val direct_grant = syscalls.index_of("val caps = spawn_full()")
expect(direct_grant).to_equal(-1)

step("all three sites take their caps from the guard")
# STALE ASSERTION FIXED 2026-08-01: this used to split on
# "val caps = spawn_authority_ambient_caps(caller)" and expect 4. The
# recipe half of master plan 5.4 moved the three sites behind
# `_spawn_caps_for(caller)`, which routes to the guard's ambient path for
# an undeclared recipe and to `spawn_authority_spawn_caps` for a migrated
# one -- so the old literal matched ZERO times and the case was RED at
# HEAD. Assert the current indirection, and that it still ends at the
# guard rather than at a raw grant.
val guarded_caps = syscalls.split("val caps = _spawn_caps_for(caller)")
expect(guarded_caps.len()).to_equal(4)
expect(syscalls).to_contain("return spawn_authority_ambient_caps(caller)")
expect(syscalls).to_contain("spawn_authority_spawn_caps(caller, recipe,")

step("all three sites ask the guard before spawning")
val checks = syscalls.split("if _ambient_spawn_denied(caller):")
expect(checks.len()).to_equal(4)

step("a refused caller gets a permission-denied result, never a task")
expect(syscalls).to_contain("return SyscallResult(value: 0 - EACCES as i64)")
expect(syscalls).to_contain("return SpawnBinaryDirectState(pid: 0 - EACCES as i64, scheduler: scheduler)")

step("the caller id comes from the scheduler, never a fabricated value")
expect(syscalls).to_contain("fn _ambient_spawn_caller(scheduler: Scheduler) -> i64:")
expect(syscalls).to_contain("scheduler.get_current().id.to_i64()")
```

</details>

#### places the seal call last in boot, but leaves it BEHIND AN OFF GATE

- init_services imports the seal entry points
- boot declares the root task before sealing
- the root task id is the kernel-origin sentinel 0
- sealing happens after the essential services are up
- the seal call is GATED, and the gate is currently OFF
- boot therefore reports a DEFERRED seal, not an armed one


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# HONESTY NOTE (2026-08-01): this case used to be titled "arms the guard
# at the end of boot service initialization" and asserted nothing but the
# TEXT POSITION of `spawn_authority_seal_bootstrap()` inside
# init_services.spl. That was a FALSE GREEN: the call it located sits
# inside `if _seal_ambient_spawn_on_boot():`, and that function is
# literally `return false`, so boot has NEVER armed the guard. The
# position checks are kept (ordering is still a real requirement) but the
# claim is now scoped to what they actually prove, and the gate's OFF
# state is asserted explicitly so flipping it cannot land silently.
step("init_services imports the seal entry points")
val init_services = file_read(INIT_SERVICES_PATH)
expect(init_services).to_contain("use os.kernel.loader.spawn_authority.")
expect(init_services).to_contain("spawn_authority_set_root_task")
expect(init_services).to_contain("spawn_authority_seal_bootstrap")

step("boot declares the root task before sealing")
val set_root_pos = init_services.index_of("spawn_authority_set_root_task(BOOT_ROOT_TASK_ID)")
val seal_pos = init_services.index_of("spawn_authority_seal_bootstrap()")
expect(set_root_pos).to_be_greater_than(-1)
expect(seal_pos).to_be_greater_than(set_root_pos)

step("the root task id is the kernel-origin sentinel 0")
expect(init_services).to_contain("val BOOT_ROOT_TASK_ID: i64 = 0")

step("sealing happens after the essential services are up")
val storage_pos = init_services.index_of("svc_storage_ok = vfs_boot_init_production()")
val display_pos = init_services.index_of("svc_display_ok = _init_display_service()")
expect(storage_pos).to_be_greater_than(-1)
expect(seal_pos).to_be_greater_than(storage_pos)
expect(seal_pos).to_be_greater_than(display_pos)

step("the seal call is GATED, and the gate is currently OFF")
val gate_pos = init_services.index_of("if _seal_ambient_spawn_on_boot():")
expect(gate_pos).to_be_greater_than(-1)
expect(seal_pos).to_be_greater_than(gate_pos)
val gate_decl = init_services.index_of("fn _seal_ambient_spawn_on_boot() -> bool:")
expect(gate_decl).to_be_greater_than(-1)
val gate_body = init_services.substring(gate_decl, gate_decl + 64)
expect(gate_body).to_contain("return false")

step("boot therefore reports a DEFERRED seal, not an armed one")
expect(init_services).to_contain("seal DEFERRED")
```

</details>

#### proves the seal is a real state change, so an armed boot would enforce

- perform the boot sequence's two calls in boot's order
- the guard is observably armed afterwards
   - Expected: spawn_authority_root_task() equals `ROOT_CALLER`
- an armed boot would keep root spawning and refuse userland ambient
   - Expected: spawn_authority_check_ambient(ROOT_CALLER) equals `0`
   - Expected: spawn_authority_check_ambient(USER_CALLER) equals `SPAWN_AUTHORITY_EPERM`
- leave the guard unsealed so case order cannot leak state


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The behavioural half the source-text case above cannot supply:
# `init_all_services()` needs a booted kernel (PMM, VFS, PCI, framebuffer)
# and cannot run inside a spec, so the guard's own API stands in for the
# boot call. Flipping `_seal_ambient_spawn_on_boot()` to true makes boot
# execute exactly this sequence.
step("perform the boot sequence's two calls in boot's order")
spawn_authority_reopen_bootstrap()
assert_false(spawn_authority_bootstrap_sealed())
spawn_authority_set_root_task(ROOT_CALLER)
spawn_authority_seal_bootstrap()

step("the guard is observably armed afterwards")
assert_true(spawn_authority_bootstrap_sealed())
expect(spawn_authority_root_task()).to_equal(ROOT_CALLER)

step("an armed boot would keep root spawning and refuse userland ambient")
expect(spawn_authority_check_ambient(ROOT_CALLER)).to_equal(0)
expect(spawn_authority_check_ambient(USER_CALLER)).to_equal(SPAWN_AUTHORITY_EPERM)

step("leave the guard unsealed so case order cannot leak state")
spawn_authority_reopen_bootstrap()
assert_false(spawn_authority_bootstrap_sealed())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane INT-1)`
- **Design:** `doc/01_research/domain/simpleos_production_host_master_plan.md (5.4)`
- **Research:** `doc/01_research/domain/simpleos_production_host_master_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `06dc430ea85d6a58de2415fabe4634ed61638e3a96af21949bdf8373e3142dce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06dc430ea85d6a58de2415fabe4634ed61638e3a96af21949bdf8373e3142dce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06dc430ea85d6a58de2415fabe4634ed61638e3a96af21949bdf8373e3142dce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl:69:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'admits every caller while the bootstrap window is open' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies a non-root caller once the bootstrap window is sealed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts each refused ambient spawn so a gate can observe it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'readmits every caller when the bootstrap window is reopened' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
