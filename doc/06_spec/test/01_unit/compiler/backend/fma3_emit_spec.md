# Fma3 Emit Specification

> 1. expect result len

<!-- sdn-diagram:id=fma3_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fma3_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fma3_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fma3_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fma3 Emit Specification

## Scenarios

### FMA3 emit_vfmadd132ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rd<8 → ~R=1, rm<8 → ~B=1, ~X=1, mmmmm=2 → 226
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=0, ~vvvv=(15-rn=1)=14, L=1(bit2=4), pp=01(1) → 14*8+5=117
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

#### byte3 is opcode 0x98

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[3] == 152
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=rd%8=0, rm=rm%8=2 → 192+0*8+2=194
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132ps_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rd>=8 → ~R=0, rm<8 → ~B=1 → 226-128=98
val result = emit_vfmadd132ps_ymm(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132ps_ymm(9, 1, 2)
expect result[2] == 117
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=9%8=1, rm=2%8=2 → 192+1*8+2=202
val result = emit_vfmadd132ps_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

### FMA3 emit_vfmadd132ps_ymm extended rn ymm9

#### byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ~vvvv=(15-rn=9)=6, L=1, pp=01 → 6*8+5=53
val result = emit_vfmadd132ps_ymm(0, 9, 2)
expect result[2] == 53
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132ps_ymm(0, 9, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132ps_ymm extended rm ymm9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rd<8 → ~R=1; rm>=8 → ~B=0 → 226-32=194
val result = emit_vfmadd132ps_ymm(0, 1, 9)
expect result[1] == 194
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=0%8=0, rm=9%8=1 → 192+0*8+1=193
val result = emit_vfmadd132ps_ymm(0, 1, 9)
expect result[4] == 193
```

</details>

### FMA3 emit_vfmadd213ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd213ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xA8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd213ps_ymm(0, 1, 2)
expect result[3] == 168
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd213ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmadd213ps_ymm extended rm ymm9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd213ps_ymm(0, 1, 9)
expect result[1] == 194
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd213ps_ymm(0, 1, 9)
expect result[4] == 193
```

</details>

### FMA3 emit_vfmadd231ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd231ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xB8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd231ps_ymm(0, 1, 2)
expect result[3] == 184
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd231ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub132ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub132ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x9A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub132ps_ymm(0, 1, 2)
expect result[3] == 154
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub132ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub132ps_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub132ps_ymm(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub132ps_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

### FMA3 emit_vfmsub213ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub213ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xAA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub213ps_ymm(0, 1, 2)
expect result[3] == 170
```

</details>

#### byte2 is 0x75

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub213ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub231ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub231ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xBA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub231ps_ymm(0, 1, 2)
expect result[3] == 186
```

</details>

#### byte2 is 0x75

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub231ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub231ps_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub231ps_ymm(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmsub231ps_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

### FMA3 emit_vfnmadd213ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfnmadd213ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xAC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfnmadd213ps_ymm(0, 1, 2)
expect result[3] == 172
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfnmadd213ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfnmadd213ps_ymm extended rn ymm9

#### byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ~vvvv=(15-rn=9)=6 → 6*8+5=53
val result = emit_vfnmadd213ps_ymm(0, 9, 2)
expect result[2] == 53
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfnmadd213ps_ymm(0, 9, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132pd_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=1 adds 128, ~vvvv=14, L=1, pp=01 → 128+14*8+5=245
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[2] == 245
```

</details>

#### byte3 is opcode 0x98

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[3] == 152
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132pd_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rd>=8 → ~R=0 → 226-128=98
val result = emit_vfmadd132pd_ymm(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vfmadd132pd_ymm(9, 1, 2)
expect result[2] == 245
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=9%8=1, rm=2%8=2 → 192+1*8+2=202
val result = emit_vfmadd132pd_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/fma3_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FMA3 emit_vfmadd132ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmadd132ps_ymm extended rd ymm9
- FMA3 emit_vfmadd132ps_ymm extended rn ymm9
- FMA3 emit_vfmadd132ps_ymm extended rm ymm9
- FMA3 emit_vfmadd213ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmadd213ps_ymm extended rm ymm9
- FMA3 emit_vfmadd231ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub132ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub132ps_ymm extended rd ymm9
- FMA3 emit_vfmsub213ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub231ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub231ps_ymm extended rd ymm9
- FMA3 emit_vfnmadd213ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfnmadd213ps_ymm extended rn ymm9
- FMA3 emit_vfmadd132pd_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmadd132pd_ymm extended rd ymm9

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
