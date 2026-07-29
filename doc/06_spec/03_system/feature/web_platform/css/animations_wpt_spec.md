# CSS Animation Frame Preservation

> Proves the supported keyframe subset at its start, midpoint, and filled end

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Animation Frame Preservation

Proves the supported keyframe subset at its start, midpoint, and filled end

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/animations_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the supported keyframe subset at its start, midpoint, and filled end
through web semantics, layout, canonical Draw IR, and exact expected-color
Engine2D coverage/count. Web Animations compositing and unsupported properties
remain outside this bounded profile.

## Scenarios

### REQ-WEB-BROWSER-003/004/006: CSS animation frames

#### should preserve the animation feature at its exact start frame

- Resolve the animation start in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation start through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the animation start in canonical web semantic and layout state")
step("Render the animation start through canonical Draw IR and Engine2D")
expect(_animation_frame_fingerprint(
    0, 0xFFDC2626u32
)).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,4,4|" +
    "preserve,1000ms,4292617766|16|0|16"
)
```

</details>

#### should preserve interpolated geometry and color at the midpoint

- Resolve the animation midpoint in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation midpoint through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the animation midpoint in canonical web semantic and layout state")
step("Render the animation midpoint through canonical Draw IR and Engine2D")
expect(_animation_frame_fingerprint(
    500, 0xFF804488u32
)).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,8,4|" +
    "preserve,1000ms,4286596232|516|0|32"
)
```

</details>

#### should preserve the filled end frame without scheduling another frame

- Resolve the animation end in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation end through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the animation end in canonical web semantic and layout state")
step("Render the animation end through canonical Draw IR and Engine2D")
expect(_animation_frame_fingerprint(
    1000, 0xFF2563EBu32
)).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,12,4|" +
    "preserve,1000ms,4280640491|-1|0|48"
)
```

</details>

<details>
<summary>Advanced: should retain linear length interpolation at the midpoint</summary>

#### should retain linear length interpolation at the midpoint

- Check the bounded animation interpolation primitives
- interpolate length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(approx(
    interpolate_length(0.0, 100.0, 0.5), 50.0
)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should retain linear timing identity</summary>

#### should retain linear timing identity

- Check the bounded animation interpolation primitives
- ease value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(approx(
    ease_value(0.5, TimingFunction.Linear), 0.5
)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should retain the ease-in slow start</summary>

#### should retain the ease-in slow start

- Check the bounded animation interpolation primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(ease_value(
    0.5, TimingFunction.EaseIn
) < 0.5).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should interpolate number values at the midpoint</summary>

#### should interpolate number values at the midpoint

- Check the bounded animation interpolation primitives
   - Expected: _interp_number_half() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(_interp_number_half()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should parse the bounded keyframes block</summary>

#### should parse the bounded keyframes block

- Parse supported CSS keyframes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse supported CSS keyframes")
val registry = extract_keyframes(
    "@keyframes fade { from { opacity: 0; } to { opacity: 1; } }"
)
expect(registry.entries.len()).to_be_greater_than(0)
```

</details>


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
