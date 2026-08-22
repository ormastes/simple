# @manual: primary

> Purpose: Prove that Actors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Actors.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RUNTIME-010 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/actors_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Actors.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-ACTORS-001
doc/01_research/feature/REQ-FEATURE-ACTORS-001.md
doc/03_plan/feature/REQ-FEATURE-ACTORS-001.md
doc/04_architecture/feature/REQ-FEATURE-ACTORS-001.md
doc/05_design/feature/REQ-FEATURE-ACTORS-001.md

## Scenarios

### Actors

#### constructs an actor with encapsulated state

- Verify: an actor instance carries its constructed state
   - Expected: a.depth equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-ACTORS-001
step("Verify: an actor instance carries its constructed state")
val a = MailboxActor(depth: 4)
expect(a.depth).to_equal(4)
```

</details>

#### runs actor methods against the actor's own state

- Verify: the method reads the actor's field and computes on it
   - Expected: a.doubled() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-ACTORS-001
step("Verify: the method reads the actor's field and computes on it")
val a = MailboxActor(depth: 21)
expect(a.doubled()).to_equal(42)
```

</details>

#### keeps two actor instances independently isolated

- Verify: sibling instances do not share state
   - Expected: a.doubled() + b.doubled() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-ACTORS-001
step("Verify: sibling instances do not share state")
val a = MailboxActor(depth: 1)
val b = MailboxActor(depth: 2)
expect(a.doubled() + b.doubled()).to_equal(6)
```

</details>

#### runs a spawned task alongside module-level actor declarations

- Verify: green_spawn executes the task body exactly once at run-all
   - Expected: before equals `0`
   - Expected: SPAWN_SEEN equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-ACTORS-001
step("Verify: green_spawn executes the task body exactly once at run-all")
SPAWN_SEEN = 0
val handle = green_spawn(spawn_body)
val before = SPAWN_SEEN
green_run_all()
expect(before).to_equal(0)
expect(SPAWN_SEEN).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2516a4895596e9517448c3900a566ffa1805e45c23ed30e30b116e96395dd6c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2516a4895596e9517448c3900a566ffa1805e45c23ed30e30b116e96395dd6c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2516a4895596e9517448c3900a566ffa1805e45c23ed30e30b116e96395dd6c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/feature/usage/actors_spec.spl
mirror: doc/06_spec/03_system/feature/usage/actors_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/actors_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/usage/actors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/actors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/actors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/actors_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs an actor with encapsulated state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/actors_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs actor methods against the actor's own state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/actors_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps two actor instances independently isolated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
