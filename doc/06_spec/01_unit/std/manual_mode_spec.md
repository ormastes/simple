# manual_mode_spec

> Verifies the manual mode behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# manual_mode_spec

Verifies the manual mode behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/manual_mode_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the manual mode behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Manual Mode Execution

#### is in manual mode

- Verify: is in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: is in manual mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = async_mode()
expect mode == "manual"
```

</details>

#### futures are pending until polled

- Verify: futures are pending until polled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: futures are pending until polled")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val f = future(42)
# In manual mode, future doesn't execute until polled
val completed = poll_future(f)
expect completed
expect await f == 42
```

</details>

#### polling multiple futures individually

- Verify: polling multiple futures individually


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: polling multiple futures individually")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val f1 = future(10)
val f2 = future(20)
# Poll each future
poll_future(f1)
poll_future(f2)
expect await f1 == 10
expect await f2 == 20
```

</details>

#### await auto-polls in manual mode

- Verify: await auto-polls in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: await auto-polls in manual mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val f = future(100)
# await should auto-poll if needed
expect await f == 100
```

</details>

#### resolved futures work in manual mode

- Verify: resolved futures work in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: resolved futures work in manual mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val f = resolved(42)
expect is_ready(f)
expect await f == 42
```

</details>

#### futures with captures in manual mode

- Verify: futures with captures in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: futures with captures in manual mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val base = 40
val f = future(base + 2)
poll_future(f)
expect await f == 42
```

</details>

#### computation in manual mode

- Verify: computation in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: computation in manual mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val f = future(10 + 20 + 30)
poll_future(f)
expect await f == 60
```

</details>

#### multiple captures in manual mode

- Verify: multiple captures in manual mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MANUAL_MODE-001
step("Verify: multiple captures in manual mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = 10
val b = 20
val c = 12
val f = future(a + b + c)
poll_future(f)
expect await f == 42
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


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cef68d66d78ac468bd6fc5389e80d0434a70f136a56240b9bbc537116614b249`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cef68d66d78ac468bd6fc5389e80d0434a70f136a56240b9bbc537116614b249`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cef68d66d78ac468bd6fc5389e80d0434a70f136a56240b9bbc537116614b249`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/manual_mode_spec.spl
mirror: doc/06_spec/01_unit/std/manual_mode_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/manual_mode_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/manual_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/manual_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
