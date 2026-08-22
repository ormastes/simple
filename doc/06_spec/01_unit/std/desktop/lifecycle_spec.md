# lifecycle_spec

> Verifies the lifecycle behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_spec

Verifies the lifecycle behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/lifecycle_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the lifecycle behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Desktop App Lifecycle

#### creates AppLifecycle instance

- Verify: creates AppLifecycle instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DESKTOP_LIFECYCLE-001
step("Verify: creates AppLifecycle instance")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val app = AppLifecycle.new("test-app")
expect app.app_id == "test-app"
```

</details>

#### converts lifecycle event to name

- Verify: converts lifecycle event to name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DESKTOP_LIFECYCLE-001
step("Verify: converts lifecycle event to name")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val name = lifecycle_event_name(LifecycleEvent.Ready)
expect name == "Ready"
```

</details>

#### registers event handlers

- Verify: registers event handlers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DESKTOP_LIFECYCLE-001
step("Verify: registers event handlers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val app = AppLifecycle.new("test-app")
val app2 = app.on(LifecycleEvent.Ready, "on_ready")
val handlers = app2.get_handlers(LifecycleEvent.Ready)
expect handlers.length() == 1
```

</details>

#### transitions app phase

- Verify: transitions app phase


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DESKTOP_LIFECYCLE-001
step("Verify: transitions app phase")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val app = AppLifecycle.new("test-app")
val running = app.set_phase(AppPhase.Running)
val phase_name = match running.phase:
    AppPhase.Initializing: "init"
    AppPhase.Running: "running"
    AppPhase.ShuttingDown: "shutdown"
expect phase_name == "running"
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

- Canonical SPipe generation for source `2c35f3ff3394f86a20a517e83ea250d0ba21858edd4e9fb8f90c41149e8f794f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c35f3ff3394f86a20a517e83ea250d0ba21858edd4e9fb8f90c41149e8f794f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c35f3ff3394f86a20a517e83ea250d0ba21858edd4e9fb8f90c41149e8f794f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/desktop/lifecycle_spec.spl
mirror: doc/06_spec/01_unit/std/desktop/lifecycle_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/desktop/lifecycle_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/desktop/lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/desktop/lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
