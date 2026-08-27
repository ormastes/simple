# Game2d Doomgeneric Port Specification

> Tests covering Doomgeneric-style game port proof.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Doomgeneric Port Specification

## Scenarios

### Doomgeneric-style game port proof

#### keeps the example on the pure std.game2d surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the example on the pure std.game2d surface
   - Expected: src contains `use std.game2d as g`
   - Expected: src does not contain `rt_sdl2_`
   - Expected: src does not contain `Steamworks`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the example on the pure std.game2d surface")
val src = _read("examples/11_advanced/game2d/doomgeneric/main.spl")
expect(src.contains("use std.game2d as g")).to_equal(true)
expect(src.contains("rt_sdl2_")).to_equal(false)
expect(src.contains("Steamworks")).to_equal(false)
```

</details>

#### proves WAD bytes, input tick, and video frame in one path

- proves WAD bytes, input tick, and video frame in one path
   - Expected: s1.wad_bytes equals `12`
   - Expected: s1.tick equals `1`
   - Expected: s1.shots equals `1`
   - Expected: frame.non_black_count() equals `160 * 100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proves WAD bytes, input tick, and video frame in one path")
val s0 = dg.DoomPortState.boot(dg.proof_wad())
val s1 = dg.doom_tick(s0, dg.DoomPortInput(forward: true, back: false, turn_left: false, turn_right: false, fire: true))
val frame = dg.render_frame(s1, 160, 100)
expect(s1.wad_bytes).to_equal(12)
expect(s1.tick).to_equal(1)
expect(s1.shots).to_equal(1)
expect(frame.non_black_count()).to_equal(160 * 100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/game2d_doomgeneric_port_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Doomgeneric-style game port proof.
- Doomgeneric-style game port proof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `621ac43680df2daf79a792720b13bffcdc1515caa04f0194a362e2e8dc227aa0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `621ac43680df2daf79a792720b13bffcdc1515caa04f0194a362e2e8dc227aa0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `621ac43680df2daf79a792720b13bffcdc1515caa04f0194a362e2e8dc227aa0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/engine/game2d_doomgeneric_port_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_doomgeneric_port_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_doomgeneric_port_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_doomgeneric_port_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_doomgeneric_port_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/engine/game2d_doomgeneric_port_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the example on the pure std.game2d surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_doomgeneric_port_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves WAD bytes, input tick, and video frame in one path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
