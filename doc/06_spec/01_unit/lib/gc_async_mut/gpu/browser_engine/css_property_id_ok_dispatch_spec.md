# Css Property Id Ok Dispatch Specification

> Tests covering css_prop_id stays in lockstep with the dispatch allowlist, apply_decls dispatch path is O(k) in declarations, not O(props), gated dispatch families stay parity-equal with the probe body.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Property Id Ok Dispatch Specification

## Scenarios

### css_prop_id stays in lockstep with the dispatch allowlist

#### every dispatch prop has a nonzero id and unknown names are zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- every dispatch prop has a nonzero id and unknown names are zero
   - Expected: missing equals `0`
   - Expected: _APPLY_DECLS_DISPATCH_PROPS.len() > 20 is true
   - Expected: css_prop_id("letter-spacing") equals `CSS_PROP_UNKNOWN`
   - Expected: css_prop_id("not-a-property") equals `CSS_PROP_UNKNOWN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("every dispatch prop has a nonzero id and unknown names are zero")
var i = 0
var missing = 0
while i < _APPLY_DECLS_DISPATCH_PROPS.len():
    if css_prop_id(_APPLY_DECLS_DISPATCH_PROPS[i]) == CSS_PROP_UNKNOWN:
        missing = missing + 1
    i = i + 1
expect(missing).to_equal(0)
# anti-vacuity: the allowlist was actually traversed
expect(_APPLY_DECLS_DISPATCH_PROPS.len() > 20).to_equal(true)
expect(css_prop_id("letter-spacing")).to_equal(CSS_PROP_UNKNOWN)
expect(css_prop_id("not-a-property")).to_equal(CSS_PROP_UNKNOWN)
```

</details>

#### mask reflects presence of declared properties

- mask reflects presence of declared properties
   - Expected: css_prop_mask_has(mask, CSS_PROP_COLOR) is true
   - Expected: css_prop_mask_has(mask, CSS_PROP_WIDTH) is true
   - Expected: empty_mask equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask reflects presence of declared properties")
val tbl: [text] = ["color", "#ff0000", "width", "10px"]
val mask = css_prop_mask(tbl)
expect(css_prop_mask_has(mask, CSS_PROP_COLOR)).to_equal(true)
expect(css_prop_mask_has(mask, CSS_PROP_WIDTH)).to_equal(true)
val empty_mask = css_prop_mask([])
expect(empty_mask).to_equal(0)
```

</details>

### apply_decls dispatch path is O(k) in declarations, not O(props)

#### 2 declarations cost at most 2*k + 2 probes

- 2 declarations cost at most 2*k + 2 probes
   - Expected: probes <= 6 is true
   - Expected: probes >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("2 declarations cost at most 2*k + 2 probes")
val st = renderer_default_style()
css_probe_reset()
apply_decls(st, "color:#ff0000;width:10px", 16)
val probes = css_probe_count()
# k=2. Pre-Stage-3 the dispatch body probed every allowlisted
# property (~25+ table scans) regardless of presence.
expect(probes <= 6).to_equal(true)
expect(probes >= 2).to_equal(true)
```

</details>

#### single declaration costs O(1) probes

- single declaration costs O(1) probes
   - Expected: probes <= 3 is true
   - Expected: probes >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single declaration costs O(1) probes")
val st = renderer_default_style()
css_probe_reset()
apply_decls(st, "z-index:3", 16)
val probes = css_probe_count()
expect(probes <= 3).to_equal(true)
expect(probes >= 1).to_equal(true)
```

</details>

### gated dispatch families stay parity-equal with the probe body

#### margin family: longhand after shorthand wins on both paths

- margin family: longhand after shorthand wins on both paths
   - Expected: a.margin_l equals `b.margin_l`
   - Expected: a.margin_l equals `9`
   - Expected: a.margin_t equals `b.margin_t`
   - Expected: a.margin_r equals `b.margin_r`
   - Expected: a.margin_b equals `b.margin_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("margin family: longhand after shorthand wins on both paths")
val d = "margin:1px 2px 3px 4px;margin-left:9px"
val a = apply_decls(renderer_default_style(), d, 16)
val b = apply_decls(renderer_default_style(), _probe_twin(d), 16)
expect(a.margin_l).to_equal(b.margin_l)
expect(a.margin_l).to_equal(9)
expect(a.margin_t).to_equal(b.margin_t)
expect(a.margin_r).to_equal(b.margin_r)
expect(a.margin_b).to_equal(b.margin_b)
```

</details>

#### margin family: shorthand after longhand wins on both paths

- margin family: shorthand after longhand wins on both paths
   - Expected: a.margin_l equals `b.margin_l`
   - Expected: a.margin_l equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("margin family: shorthand after longhand wins on both paths")
val d = "margin-left:9px;margin:1px 2px 3px 4px"
val a = apply_decls(renderer_default_style(), d, 16)
val b = apply_decls(renderer_default_style(), _probe_twin(d), 16)
expect(a.margin_l).to_equal(b.margin_l)
expect(a.margin_l).to_equal(4)
```

</details>

#### border-radius family parity across paths

- border-radius family parity across paths
   - Expected: a.border_radius_tl_px equals `b.border_radius_tl_px`
   - Expected: a.border_radius_br_px equals `b.border_radius_br_px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("border-radius family parity across paths")
val d = "border-radius:5px;border-top-left-radius:8px"
val a = apply_decls(renderer_default_style(), d, 16)
val b = apply_decls(renderer_default_style(), _probe_twin(d), 16)
expect(a.border_radius_tl_px).to_equal(b.border_radius_tl_px)
expect(a.border_radius_br_px).to_equal(b.border_radius_br_px)
```

</details>

#### gap / overflow / box-shadow / color / z-index parity across paths

- gap / overflow / box-shadow / color / z-index parity across paths
   - Expected: a.gap_px equals `b.gap_px`
   - Expected: a.gap_px equals `7`
   - Expected: a.overflow_hidden equals `b.overflow_hidden`
   - Expected: a.box_shadow_raw equals `b.box_shadow_raw`
   - Expected: a.fg equals `b.fg`
   - Expected: a.z_index equals `b.z_index`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gap / overflow / box-shadow / color / z-index parity across paths")
val d = "gap:7px;overflow:hidden;box-shadow:none;color:#ff0000;z-index:3"
val a = apply_decls(renderer_default_style(), d, 16)
val b = apply_decls(renderer_default_style(), _probe_twin(d), 16)
expect(a.gap_px).to_equal(b.gap_px)
expect(a.gap_px).to_equal(7)
expect(a.overflow_hidden).to_equal(b.overflow_hidden)
expect(a.box_shadow_raw).to_equal(b.box_shadow_raw)
expect(a.fg).to_equal(b.fg)
expect(a.z_index).to_equal(b.z_index)
```

</details>

#### absent properties leave style untouched on the dispatch path

- absent properties leave style untouched on the dispatch path
   - Expected: a.width_px equals `10`
   - Expected: a.fg equals `base.fg`
   - Expected: a.margin_l equals `base.margin_l`
   - Expected: a.gap_px equals `base.gap_px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("absent properties leave style untouched on the dispatch path")
val base = renderer_default_style()
val a = apply_decls(renderer_default_style(), "width:10px", 16)
expect(a.width_px).to_equal(10)
expect(a.fg).to_equal(base.fg)
expect(a.margin_l).to_equal(base.margin_l)
expect(a.gap_px).to_equal(base.gap_px)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering css_prop_id stays in lockstep with the dispatch allowlist, apply_decls dispatch path is O(k) in declarations, not O(props), gated dispatch families stay parity-equal with the probe body.
- css_prop_id stays in lockstep with the dispatch allowlist
- apply_decls dispatch path is O(k) in declarations, not O(props)
- gated dispatch families stay parity-equal with the probe body

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92aee82396d573cb67e2d4ea1342c2b864354594104137c9646c3a689c615504`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92aee82396d573cb67e2d4ea1342c2b864354594104137c9646c3a689c615504`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92aee82396d573cb67e2d4ea1342c2b864354594104137c9646c3a689c615504`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every dispatch prop has a nonzero id and unknown names are zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mask reflects presence of declared properties' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_property_id_ok_dispatch_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '2 declarations cost at most 2*k + 2 probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
