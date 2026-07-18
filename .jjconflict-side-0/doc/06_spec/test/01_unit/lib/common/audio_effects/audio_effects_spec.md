# Audio Effects Specification

> <details>

<!-- sdn-diagram:id=audio_effects_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audio_effects_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audio_effects_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audio_effects_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio Effects Specification

## Scenarios

### Audio Effects Stubs

#### Pitch control

#### rt_audio_set_pitch returns 0

- expect rt audio set pitch


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_audio_set_pitch(1, 1.0) == 0
```

</details>

#### Filter stubs

#### rt_audio_add_lowpass returns 0

- expect rt audio add lowpass


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_audio_add_lowpass(1, 1000.0) == 0
```

</details>

#### rt_audio_add_highpass returns 0

- expect rt audio add highpass


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_audio_add_highpass(1, 500.0) == 0
```

</details>

#### Effect stubs

#### rt_audio_add_reverb returns 0

- expect rt audio add reverb


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_audio_add_reverb(1, 0.5, 0.3) == 0
```

</details>

#### rt_audio_add_delay returns 0

- expect rt audio add delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_audio_add_delay(1, 200.0, 0.4) == 0
```

</details>

#### rt_audio_remove_effect returns 0

- expect rt audio remove effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_audio_remove_effect(1, 2) == 0
```

</details>

#### rt_audio_clear_effects returns 0

- expect rt audio clear effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_audio_clear_effects(1) == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/audio_effects/audio_effects_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Audio Effects Stubs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
