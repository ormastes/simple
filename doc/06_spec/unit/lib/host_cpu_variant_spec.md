# host_cpu_variant_spec

> Purpose: Host CPU runtime variant selection — 20 unit tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# host_cpu_variant_spec

Purpose: Host CPU runtime variant selection — 20 unit tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/host_cpu_variant_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Host CPU runtime variant selection — 20 unit tests.
Audience: runtime engineers who own io_runtime variant dispatch.

Covers SIMD tier ranking, hardware clamping, dispatch name qualification,
loader probing, manifest entries, and variant selection with fallback.
All helpers are self-contained (no external imports beyond io_runtime).

## Scenarios

### host CPU runtime variant selection

#### all 20 host CPU variant checks pass (tier ranking, clamping, dispatch, probing, manifest, fallback)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- all 20 host CPU variant checks pass (tier ranking, clamping, dispatch, probing, manifest, fallback)
   - Expected: check_failures < 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 20 host CPU variant checks pass (tier ranking, clamping, dispatch, probing, manifest, fallback)")
_run_all_host_cpu_variant_checks()
# oracle: every pinned behavior above must hold; fail-closed on any FAIL label
expect(check_failures < 1).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f2610f4f4eeb19820236319e4352bbe0b1c9b9dfc05341c4081fe1379b49e9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f2610f4f4eeb19820236319e4352bbe0b1c9b9dfc05341c4081fe1379b49e9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f2610f4f4eeb19820236319e4352bbe0b1c9b9dfc05341c4081fe1379b49e9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/unit/lib/host_cpu_variant_spec.spl
mirror: doc/06_spec/unit/lib/host_cpu_variant_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/host_cpu_variant_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/host_cpu_variant_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/host_cpu_variant_spec.spl:307:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all 20 host CPU variant checks pass (tier ranking, clamping, dispatch, probing, manifest, fallback)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
