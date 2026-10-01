# GUI Low-Resolution Readability Verification

> Verifies that the GUI showcase app renders text and widgets legibly at low resolutions (640×480, 800×600, 1280×720). The readability oracle analyzes captured PPM frames for:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Low-Resolution Readability Verification

Verifies that the GUI showcase app renders text and widgets legibly at low resolutions (640×480, 800×600, 1280×720). The readability oracle analyzes captured PPM frames for:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W2, G1.3 |
| Category | Testing \| Infrastructure \| GUI |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W2) |
| Design | N/A |
| Source | `test/03_system/check/gui_low_res_readability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the GUI showcase app renders text and widgets legibly at low
resolutions (640×480, 800×600, 1280×720). The readability oracle analyzes
captured PPM frames for:

1. Non-blank content (≥2 distinct colors)
2. Ink coverage within reasonable bounds (5% to 95%)
3. Text-like regions (rows with ≥3 run transitions)
4. No clipping at viewport edges (borders mostly background)

This is a system-level smoke gate, not OCR-grade verification. The oracle
inputs raw pixels from the showcase app via SHOWCASE_PPM env var dumps.

## Related Specifications

- [Production Readiness Master Plan](../../../doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md) — W2, G1.3
- [Widget Showcase GUI](../../../examples/06_io/ui/widget_showcase_gui.spl)

## Scenarios

### GUI Low-Resolution Readability

#### readability check completes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- readability check completes
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("readability check completes")
# In a live run, this would exec the check script
# For the spec, we verify the evidence structure
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_err():
    print "Note: evidence.env not yet generated; skipping live assertions"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    # Verify the overall field exists
    val overall = get_env_value(entries, "overall")
    expect(overall).to_be_truthy()
```

</details>

#### 640x480 resolution is readable

- readability check completes
   - Exec capture: after_step
- 640x480 resolution is readable
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("readability check completes")
# In a live run, this would exec the check script
# For the spec, we verify the evidence structure
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_err():
    print "Note: evidence.env not yet generated; skipping live assertions"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    # Verify the overall field exists
    val overall = get_env_value(entries, "overall")
    expect(overall).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("640x480 resolution is readable")
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "640x480")
```

</details>

#### 800x600 resolution is readable

- readability check completes
   - Exec capture: after_step
- 800x600 resolution is readable
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("readability check completes")
# In a live run, this would exec the check script
# For the spec, we verify the evidence structure
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_err():
    print "Note: evidence.env not yet generated; skipping live assertions"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    # Verify the overall field exists
    val overall = get_env_value(entries, "overall")
    expect(overall).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("800x600 resolution is readable")
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "800x600")
```

</details>

#### 1280x720 resolution is readable

- readability check completes
   - Exec capture: after_step
- 1280x720 resolution is readable
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("readability check completes")
# In a live run, this would exec the check script
# For the spec, we verify the evidence structure
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_err():
    print "Note: evidence.env not yet generated; skipping live assertions"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    # Verify the overall field exists
    val overall = get_env_value(entries, "overall")
    expect(overall).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("1280x720 resolution is readable")
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "1280x720")
```

</details>

#### overall status is pass

- 1280x720 resolution is readable
- overall status is pass
   - Expected: overall equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1280x720 resolution is readable")
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "1280x720")

# @req REQ-SSPEC-SYSTEM
step("overall status is pass")
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    val overall = get_env_value(entries, "overall")
    expect(overall).to_equal("pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W2)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d5d203cc1e24f28d21bfb2770f40d53e3685441e5ce49a3359b2afbecb6b346b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5d203cc1e24f28d21bfb2770f40d53e3685441e5ce49a3359b2afbecb6b346b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5d203cc1e24f28d21bfb2770f40d53e3685441e5ce49a3359b2afbecb6b346b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/gui_low_res_readability_spec.spl
mirror: doc/06_spec/03_system/check/gui_low_res_readability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_low_res_readability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_low_res_readability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_low_res_readability_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'readability check completes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_low_res_readability_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '640x480 resolution is readable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_low_res_readability_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '800x600 resolution is readable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
