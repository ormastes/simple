# Game2d Backend Facade Specification

> Tests covering nogc_async_mut game2d backend facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Backend Facade Specification

## Scenarios

### nogc_async_mut game2d backend facade

#### re-exports deterministic backend records and hash helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports deterministic backend records and hash helpers
   - Expected: frame_hash([]) equals `FNV_OFFSET_BASIS`
   - Expected: frame_hash_hex([]).len() equals `18`
   - Expected: cfg.width equals `800`
   - Expected: Window.null().raw equals `0`
   - Expected: Event.none().kind equals `none`
   - Expected: backend.width equals `2`
   - Expected: backend.golden_diff(backend.frame_hash()) equals ``
   - Expected: sdl.width equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports deterministic backend records and hash helpers")
expect(frame_hash([])).to_equal(FNV_OFFSET_BASIS)
expect(frame_hash_hex([]).len()).to_equal(18)
val cfg = WindowConfig.default()
expect(cfg.width).to_equal(800)
expect(Window.null().raw).to_equal(0)
expect(Event.none().kind).to_equal("none")
val backend = HeadlessBackend.create(2, 2)
expect(backend.width).to_equal(2)
expect(backend.golden_diff(backend.frame_hash())).to_equal("")
val sdl = SdlBackend.create()
expect(sdl.width).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/game2d/backend/game2d_backend_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut game2d backend facade.
- nogc_async_mut game2d backend facade

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

- Canonical SPipe generation for source `757c722a595928b7a989aca924041fc7f55df85b2720a4db1962a60962e4883d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `757c722a595928b7a989aca924041fc7f55df85b2720a4db1962a60962e4883d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `757c722a595928b7a989aca924041fc7f55df85b2720a4db1962a60962e4883d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/nogc_async_mut/game2d/backend/game2d_backend_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/game2d/backend/game2d_backend_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/game2d/backend/game2d_backend_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/game2d/backend/game2d_backend_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/game2d/backend/game2d_backend_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/game2d/backend/game2d_backend_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports deterministic backend records and hash helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
