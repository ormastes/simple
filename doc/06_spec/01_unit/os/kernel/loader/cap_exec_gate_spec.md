# Exec Capability Gate Specification (WP-21)

> `src/os/kernel/loader/cap_exec_gate.spl`'s `exec_cap_check(caller, path)` previously built a fresh, empty `CapabilityManager` per call — its `records: [TaskCapRecord]` store starts empty and nothing ever populates it for an fs-exec caller, so any nonzero caller was unconditionally denied regardless of what capabilities it actually held. That made the gate impossible to prove correct: a deny-only spec against it would pass whether or not the underlying capability-matching logic works at all.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exec Capability Gate Specification (WP-21)

`src/os/kernel/loader/cap_exec_gate.spl`'s `exec_cap_check(caller, path)` previously built a fresh, empty `CapabilityManager` per call — its `records: [TaskCapRecord]` store starts empty and nothing ever populates it for an fs-exec caller, so any nonzero caller was unconditionally denied regardless of what capabilities it actually held. That made the gate impossible to prove correct: a deny-only spec against it would pass whether or not the underlying capability-matching logic works at all.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-P2-EXEC-CAP-GATE |
| Category | Runtime / Security |
| Difficulty | 2/5 |
| Status | Implemented (real logic); caller-identity threading still open |
| Plan | doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md (WP-21) |
| Source | `test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`src/os/kernel/loader/cap_exec_gate.spl`'s `exec_cap_check(caller, path)`
previously built a fresh, empty `CapabilityManager` per call — its
`records: [TaskCapRecord]` store starts empty and nothing ever populates it
for an fs-exec caller, so any nonzero caller was unconditionally denied
regardless of what capabilities it actually held. That made the gate
impossible to prove correct: a deny-only spec against it would pass whether
or not the underlying capability-matching logic works at all.

`exec_cap_check_caps(caps: CapabilitySet, path: text)` is the real check,
built on `CapabilitySet.has(...)` — the SAME model `TaskControlBlock.capabilities`
and `spawn_authority.spl` already use in production, instead of a throwaway
per-call record store. This spec proves BOTH directions: a caller pledged to
a set lacking FileExec/ProcessSpawn is denied, and a caller holding both
rights is allowed — the pair that makes either assertion meaningful.

Caller-identity threading (mapping a real fs-exec `caller: i64` to its real
`CapabilitySet` at the `fs_exec_spawn_as` call site) remains a separate, open
gap — see `doc/08_tracking/bug/exec_cap_check_caller_identity_not_threaded_2026-08-07.md`.

## Scenarios

### exec_cap_check_caps (real capability logic, WP-21)

#### denies a caller pledged to a set with NEITHER right

- denies a caller pledged to a set with NEITHER right
- build a deny-all pledged set
- check exec capability against it
   - Expected: rc equals `EACCES`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies a caller pledged to a set with NEITHER right")
step("build a deny-all pledged set")
val caps = CapabilitySet.empty()
step("check exec capability against it")
val rc = exec_cap_check_caps(caps, EXEC_PATH)
expect(rc).to_equal(EACCES)
```

</details>

#### denies a caller pledged to ProcessSpawn only (missing FileExec)

- denies a caller pledged to ProcessSpawn only (missing FileExec)
- pledge only ProcessSpawn
- check exec capability against it
   - Expected: rc equals `EACCES`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies a caller pledged to ProcessSpawn only (missing FileExec)")
step("pledge only ProcessSpawn")
val caps = _pledged([CapabilityKind.ProcessSpawn])
step("check exec capability against it")
val rc = exec_cap_check_caps(caps, EXEC_PATH)
expect(rc).to_equal(EACCES)
```

</details>

#### denies a caller pledged to FileExec only (missing ProcessSpawn)

- denies a caller pledged to FileExec only (missing ProcessSpawn)
- pledge only FileExec for the target path
- check exec capability against it
   - Expected: rc equals `EACCES`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies a caller pledged to FileExec only (missing ProcessSpawn)")
step("pledge only FileExec for the target path")
val caps = _pledged([CapabilityKind.FileExec(path_prefix: EXEC_PATH)])
step("check exec capability against it")
val rc = exec_cap_check_caps(caps, EXEC_PATH)
expect(rc).to_equal(EACCES)
```

</details>

#### denies FileExec pledged to a DIFFERENT path prefix

- denies FileExec pledged to a DIFFERENT path prefix
- pledge FileExec + ProcessSpawn, but scoped to another path
- check exec capability against the real target path
   - Expected: rc equals `EACCES`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies FileExec pledged to a DIFFERENT path prefix")
step("pledge FileExec + ProcessSpawn, but scoped to another path")
val caps = _pledged([
    CapabilityKind.FileExec(path_prefix: "/sys/apps/other.smf"),
    CapabilityKind.ProcessSpawn
])
step("check exec capability against the real target path")
val rc = exec_cap_check_caps(caps, EXEC_PATH)
expect(rc).to_equal(EACCES)
```

</details>

#### allows a caller pledged to BOTH FileExec(path) and ProcessSpawn

- allows a caller pledged to BOTH FileExec(path) and ProcessSpawn
- pledge exactly the two required rights
- check exec capability against it
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allows a caller pledged to BOTH FileExec(path) and ProcessSpawn")
step("pledge exactly the two required rights")
val caps = _pledged([
    CapabilityKind.FileExec(path_prefix: EXEC_PATH),
    CapabilityKind.ProcessSpawn
])
step("check exec capability against it")
val rc = exec_cap_check_caps(caps, EXEC_PATH)
expect(rc).to_equal(0)
```

</details>

#### allows the unpledged ambient-full set

- allows the unpledged ambient-full set
- build the ambient-full set (root/boot only in production)
- check exec capability against it
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allows the unpledged ambient-full set")
step("build the ambient-full set (root/boot only in production)")
val caps = CapabilitySet.full()
step("check exec capability against it")
val rc = exec_cap_check_caps(caps, EXEC_PATH)
expect(rc).to_equal(0)
```

</details>

### exec_cap_check (scalar-caller ABI, unchanged scope)

#### passes the kernel-origin sentinel caller == 0

- passes the kernel-origin sentinel caller == 0
- call with caller 0
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("passes the kernel-origin sentinel caller == 0")
step("call with caller 0")
val rc = exec_cap_check(0, EXEC_PATH)
expect(rc).to_equal(0)
```

</details>

#### denies any nonzero caller (no capability set threadable at this ABI)

- denies any nonzero caller (no capability set threadable at this ABI)
- call with a nonzero caller id
   - Expected: rc equals `EACCES`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies any nonzero caller (no capability set threadable at this ABI)")
step("call with a nonzero caller id")
val rc = exec_cap_check(42, EXEC_PATH)
expect(rc).to_equal(EACCES)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md (WP-21)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b8bae81415a00850796c148d59c26fa46c224ff50418038a0225701c3734650`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b8bae81415a00850796c148d59c26fa46c224ff50418038a0225701c3734650`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b8bae81415a00850796c148d59c26fa46c224ff50418038a0225701c3734650`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/cap_exec_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/cap_exec_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/cap_exec_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies a caller pledged to a set with NEITHER right' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies a caller pledged to ProcessSpawn only (missing FileExec)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies a caller pledged to FileExec only (missing ProcessSpawn)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
