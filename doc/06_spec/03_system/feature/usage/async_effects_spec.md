# async_effects_spec

> Purpose: async effect behavior is observed through the production async

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_effects_spec

Purpose: async effect behavior is observed through the production async

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RUNTIME-011 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/async_effects_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: async effect behavior is observed through the production async
primitives (std.async_core Poll, std.async.future Future) — readiness,
suspension, and value transport across poll boundaries — instead of a pending
scaffold. Audience: runtime engineers maintaining the async core.

## Scenarios

### Async Effects

#### a ready computation resolves without suspension

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: Poll.Ready reports ready and unwraps its value
   - Expected: p.is_ready() is true
   - Expected: p.is_pending() is false
   - Expected: p.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Verify: Poll.Ready reports ready and unwraps its value")
val p: Poll<i64> = Poll.Ready(42)
expect(p.is_ready()).to_equal(true)  # oracle: ready poll is ready
expect(p.is_pending()).to_equal(false)  # oracle: ready poll is not pending
expect(p.unwrap()).to_equal(42)  # oracle: transported value survives the poll boundary
```

</details>

#### a pending computation suspends instead of resolving

- Verify: Poll.Pending reports suspension
   - Expected: p.is_pending() is true
   - Expected: p.is_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Verify: Poll.Pending reports suspension")
val p: Poll<i64> = Poll.Pending
expect(p.is_pending()).to_equal(true)  # oracle: pending poll reports suspension
expect(p.is_ready()).to_equal(false)  # oracle: pending poll is not ready
```

</details>

#### a future carries its effectful result across the await boundary

- Verify: resolved future polls to a ready value and maps onward
   - Expected: f.is_ready() is true
   - Expected: f.poll().unwrap() equals `7`
   - Expected: mapped.poll().unwrap() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Verify: resolved future polls to a ready value and maps onward")
val f = Future.from_value(7)
expect(f.is_ready()).to_equal(true)  # oracle: eager future is immediately resolvable
expect(f.poll().unwrap()).to_equal(7)  # oracle: value crosses the await boundary intact
val mapped = f.map(fn (x): x + 1)
expect(mapped.poll().unwrap()).to_equal(8)  # oracle: mapped future transports the transformed value
```

</details>

#### a pending future stays suspended until it becomes ready

- Verify: pending future polls pending, not ready
   - Expected: f.is_ready() is false
   - Expected: f.poll().is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Verify: pending future polls pending, not ready")
val f: Future<i64> = Future.pending()
expect(f.is_ready()).to_equal(false)  # oracle: pending future suspends
expect(f.poll().is_pending()).to_equal(true)  # oracle: polling does not fabricate readiness
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e5204c38f067cbc1ca6d07c3dc5deea327025ba2c8fd32aff42558efa68df2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e5204c38f067cbc1ca6d07c3dc5deea327025ba2c8fd32aff42558efa68df2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e5204c38f067cbc1ca6d07c3dc5deea327025ba2c8fd32aff42558efa68df2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/async_effects_spec.spl
mirror: doc/06_spec/03_system/feature/usage/async_effects_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/async_effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/async_effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/async_effects_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a ready computation resolves without suspension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/async_effects_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a pending computation suspends instead of resolving' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/async_effects_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a future carries its effectful result across the await boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
