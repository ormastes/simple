# CSS Paint Pass — Coverage Closure (partial)

> `layout_paint.spl` had zero test/ references before this spec. This spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Paint Pass — Coverage Closure (partial)

`layout_paint.spl` had zero test/ references before this spec. This spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/browser_engine/layout_paint_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`layout_paint.spl` had zero test/ references before this spec. This spec
closes `_apply_opacity` fully (all four branches).

`_paint_box` was deleted 2026-08-17: it was latent dead code written against
a nonexistent BeLayoutBox shape (`box.node`, `content_*` as fields where the
real class exposes methods) and stale dom_accessors contracts, with zero
callers. The real BeLayoutBox contract is pinned by
`layout_paint_contract_pin_spec.spl`; live painters are `layout.spl:paint_box`
and `browser_renderer.spl:_browser_paint_boxes`.

## Scenarios

### _apply_opacity (closure)

#### returns the color unchanged at full opacity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the color unchanged at full opacity
   - Expected: _apply_opacity(0xFF112233, 1.0) equals `0xFF112233`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the color unchanged at full opacity")
expect(_apply_opacity(0xFF112233, 1.0)).to_equal(0xFF112233)
```

</details>

#### zeroes the alpha channel at zero opacity

- zeroes the alpha channel at zero opacity
   - Expected: _apply_opacity(0xFF112233, 0.0) equals `0x00112233`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zeroes the alpha channel at zero opacity")
expect(_apply_opacity(0xFF112233, 0.0)).to_equal(0x00112233)
```

</details>

#### scales the alpha channel for partial opacity

- scales the alpha channel for partial opacity
   - Expected: _apply_opacity(0xFF000000, 0.5) equals `0x7F000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scales the alpha channel for partial opacity")
expect(_apply_opacity(0xFF000000, 0.5)).to_equal(0x7F000000)
```

</details>

#### preserves RGB bits while blending

- preserves RGB bits while blending
   - Expected: _apply_opacity(0x80ABCDEF, 0.5) & 0x00FFFFFF equals `0x00ABCDEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves RGB bits while blending")
expect(_apply_opacity(0x80ABCDEF, 0.5) & 0x00FFFFFF).to_equal(0x00ABCDEF)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ee81bc8244352a8ab29c4284397abd13b436ab93822dbdf8603edfbb1d6642e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ee81bc8244352a8ab29c4284397abd13b436ab93822dbdf8603edfbb1d6642e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ee81bc8244352a8ab29c4284397abd13b436ab93822dbdf8603edfbb1d6642e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/browser_engine/layout_paint_coverage_closure_spec.spl
mirror: doc/06_spec/unit/browser_engine/layout_paint_coverage_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/layout_paint_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/layout_paint_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/layout_paint_coverage_closure_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the color unchanged at full opacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/layout_paint_coverage_closure_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zeroes the alpha channel at zero opacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/layout_paint_coverage_closure_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scales the alpha channel for partial opacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
