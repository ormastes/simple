# Hrtf Specification

> <details>

<!-- sdn-diagram:id=hrtf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hrtf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hrtf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hrtf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hrtf Specification

## Scenarios

### HRTFData

#### starts with zero entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = HRTFData.new(44100)
expect(data.entry_count()).to_equal(0)
```

</details>

#### adds entries

1. var data = HRTFData new
2. data add entry
3. data add entry
   - Expected: data.entry_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = HRTFData.new(48000)
data.add_entry(0.0, 0.0, 5, 5, 1.0, 1.0)
data.add_entry(90.0, 0.0, 10, 3, 0.8, 0.5)
expect(data.entry_count()).to_equal(2)
```

</details>

#### finds nearest entry by azimuth and elevation

1. var data = HRTFData new
2. data add entry
3. data add entry
4. data add entry
   - Expected: e.azimuth equals `90.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = HRTFData.new(44100)
data.add_entry(0.0, 0.0, 5, 5, 1.0, 1.0)
data.add_entry(90.0, 0.0, 10, 3, 0.8, 0.5)
data.add_entry(180.0, 0.0, 8, 8, 0.6, 0.6)
val entry = data.find_nearest(85.0, 0.0)
if val Some(e) = entry:
    expect(e.azimuth).to_equal(90.0)
```

</details>

#### finds nearest with elevation

1. var data = HRTFData new
2. data add entry
3. data add entry
4. data add entry
   - Expected: e.elevation equals `45.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = HRTFData.new(44100)
data.add_entry(0.0, 0.0, 5, 5, 1.0, 1.0)
data.add_entry(0.0, 45.0, 7, 7, 0.9, 0.9)
data.add_entry(0.0, 90.0, 9, 9, 0.7, 0.7)
val entry = data.find_nearest(0.0, 40.0)
if val Some(e) = entry:
    expect(e.elevation).to_equal(45.0)
```

</details>

### HRTFProcessor

#### starts with no sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = HRTFData.new(44100)
val proc = HRTFProcessor.new(data)
expect(proc.source_count()).to_equal(0)
```

</details>

#### adds and tracks sources

1. var proc = HRTFProcessor new
2. proc add source
3. proc add source
   - Expected: proc.source_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = HRTFData.new(44100)
var proc = HRTFProcessor.new(data)
proc.add_source(1, 5.0, 0.0, 3.0)
proc.add_source(2, -3.0, 1.0, 0.0)
expect(proc.source_count()).to_equal(2)
```

</details>

#### updates source position

1. var proc = HRTFProcessor new
2. proc add source
3. proc update source position
   - Expected: s.position_x equals `10.0`
   - Expected: s.position_y equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = HRTFData.new(44100)
var proc = HRTFProcessor.new(data)
proc.add_source(1, 0.0, 0.0, 0.0)
proc.update_source_position(1, 10.0, 5.0, 2.0)
val src = proc.get_source(1)
if val Some(s) = src:
    expect(s.position_x).to_equal(10.0)
    expect(s.position_y).to_equal(5.0)
```

</details>

#### sets listener position

1. var proc = HRTFProcessor new
2. proc set listener position
   - Expected: proc.source_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = HRTFData.new(44100)
var proc = HRTFProcessor.new(data)
proc.set_listener_position(1.0, 2.0, 3.0)
expect(proc.source_count()).to_equal(0)
```

</details>

#### returns nil for unknown source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = HRTFData.new(44100)
val proc = HRTFProcessor.new(data)
val src = proc.get_source(999)
expect(proc.source_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/hrtf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HRTFData
- HRTFProcessor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
