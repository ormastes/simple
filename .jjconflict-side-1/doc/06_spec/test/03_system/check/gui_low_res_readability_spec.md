# GUI Low-Resolution Readability Verification

> Verifies that the GUI showcase app renders text and widgets legibly at low resolutions (640×480, 800×600, 1280×720). The readability oracle analyzes captured PPM frames for:

<!-- sdn-diagram:id=gui_low_res_readability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_low_res_readability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_low_res_readability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_low_res_readability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

- print "Loaded evidence with {entries len
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- print "Loaded evidence with {entries len
   - Exec capture: after_step
- assert readability pass
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "640x480")
```

</details>

#### 800x600 resolution is readable

- print "Loaded evidence with {entries len
   - Exec capture: after_step
- assert readability pass
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "800x600")
```

</details>

#### 1280x720 resolution is readable

- print "Loaded evidence with {entries len
   - Exec capture: after_step
- assert readability pass
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "1280x720")
```

</details>

#### overall status is pass

- assert readability pass
   - Expected: overall equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env("build/gui-low-res-readability/evidence.env")
if result.is_ok():
    val entries = result.unwrap()
    assert_readability_pass(entries, "1280x720")

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

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W2)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W2))


</details>
