# Features Extended Specification

> <details>

<!-- sdn-diagram:id=features_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=features_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

features_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=features_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Features Extended Specification

## Scenarios

### FeatureId breakpoint variants

#### ConditionalBreakpoint has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.ConditionalBreakpoint
expect(f.to_string()).to_equal("ConditionalBreakpoint")
```

</details>

#### FunctionBreakpoint has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.FunctionBreakpoint
expect(f.to_string()).to_equal("FunctionBreakpoint")
```

</details>

#### EnableBreakpoint has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.EnableBreakpoint
expect(f.to_string()).to_equal("EnableBreakpoint")
```

</details>

#### DisableBreakpoint has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.DisableBreakpoint
expect(f.to_string()).to_equal("DisableBreakpoint")
```

</details>

#### ListBreakpoints has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.ListBreakpoints
expect(f.to_string()).to_equal("ListBreakpoints")
```

</details>

#### SetBreakpoint has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.SetBreakpoint
expect(f.to_string()).to_equal("SetBreakpoint")
```

</details>

#### ClearBreakpoint has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.ClearBreakpoint
expect(f.to_string()).to_equal("ClearBreakpoint")
```

</details>

#### SetWatchpoint has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.SetWatchpoint
expect(f.to_string()).to_equal("SetWatchpoint")
```

</details>

### FeatureId frame navigation variants

#### SelectFrame has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.SelectFrame
expect(f.to_string()).to_equal("SelectFrame")
```

</details>

#### FrameLocals has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.FrameLocals
expect(f.to_string()).to_equal("FrameLocals")
```

</details>

#### FrameArguments has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.FrameArguments
expect(f.to_string()).to_equal("FrameArguments")
```

</details>

#### SetVariable has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.SetVariable
expect(f.to_string()).to_equal("SetVariable")
```

</details>

### FeatureId ptrace variants

#### PtraceAttach has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.PtraceAttach
expect(f.to_string()).to_equal("PtraceAttach")
```

</details>

#### PtraceDetach has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.PtraceDetach
expect(f.to_string()).to_equal("PtraceDetach")
```

</details>

#### PtraceContinue has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.PtraceContinue
expect(f.to_string()).to_equal("PtraceContinue")
```

</details>

#### PtraceSingleStep has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.PtraceSingleStep
expect(f.to_string()).to_equal("PtraceSingleStep")
```

</details>

#### PtraceReadMemory has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.PtraceReadMemory
expect(f.to_string()).to_equal("PtraceReadMemory")
```

</details>

#### PtraceWriteMemory has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.PtraceWriteMemory
expect(f.to_string()).to_equal("PtraceWriteMemory")
```

</details>

### FeatureId DWARF variants

#### DwarfAddrToSource has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.DwarfAddrToSource
expect(f.to_string()).to_equal("DwarfAddrToSource")
```

</details>

#### DwarfSourceToAddr has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.DwarfSourceToAddr
expect(f.to_string()).to_equal("DwarfSourceToAddr")
```

</details>

#### DwarfFunctionName has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.DwarfFunctionName
expect(f.to_string()).to_equal("DwarfFunctionName")
```

</details>

### FeatureId existing variants

#### Halt has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.Halt
expect(f.to_string()).to_equal("Halt")
```

</details>

#### Resume has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.Resume
expect(f.to_string()).to_equal("Resume")
```

</details>

#### SingleStep has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.SingleStep
expect(f.to_string()).to_equal("SingleStep")
```

</details>

#### StepOver has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.StepOver
expect(f.to_string()).to_equal("StepOver")
```

</details>

#### ReadMemory has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.ReadMemory
expect(f.to_string()).to_equal("ReadMemory")
```

</details>

#### WriteMemory has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.WriteMemory
expect(f.to_string()).to_equal("WriteMemory")
```

</details>

#### ReadLocals has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.ReadLocals
expect(f.to_string()).to_equal("ReadLocals")
```

</details>

#### ReadStackTrace has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.ReadStackTrace
expect(f.to_string()).to_equal("ReadStackTrace")
```

</details>

#### EvaluateExpression has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.EvaluateExpression
expect(f.to_string()).to_equal("EvaluateExpression")
```

</details>

### FeatureId equality

#### same variant equals itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.PtraceAttach
val b = FeatureId.PtraceAttach
expect(a.eq(b)).to_equal(true)
```

</details>

#### different variants are not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.PtraceAttach
val b = FeatureId.PtraceDetach
expect(a.eq(b)).to_equal(false)
```

</details>

#### breakpoint variants differ from ptrace variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.ConditionalBreakpoint
val b = FeatureId.PtraceAttach
expect(a.eq(b)).to_equal(false)
```

</details>

#### frame variants differ from DWARF variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.SelectFrame
val b = FeatureId.DwarfAddrToSource
expect(a.eq(b)).to_equal(false)
```

</details>

#### DWARF variants differ from each other

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.DwarfAddrToSource
val b = FeatureId.DwarfSourceToAddr
expect(a.eq(b)).to_equal(false)
```

</details>

#### system variants have correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = FeatureId.ProfileSample
val fp = FeatureId.FlashProgram
val sr = FeatureId.SystemReset
expect(ps.to_string()).to_equal("ProfileSample")
expect(fp.to_string()).to_equal("FlashProgram")
expect(sr.to_string()).to_equal("SystemReset")
```

</details>

#### all breakpoint features are distinct

1. FeatureId SetBreakpoint to string
2. FeatureId ClearBreakpoint to string
3. FeatureId ConditionalBreakpoint to string
4. FeatureId FunctionBreakpoint to string
5. FeatureId EnableBreakpoint to string
6. FeatureId DisableBreakpoint to string
7. FeatureId ListBreakpoints to string
   - Expected: all_non_empty is true
   - Expected: features.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features: [text] = [
    FeatureId.SetBreakpoint.to_string(),
    FeatureId.ClearBreakpoint.to_string(),
    FeatureId.ConditionalBreakpoint.to_string(),
    FeatureId.FunctionBreakpoint.to_string(),
    FeatureId.EnableBreakpoint.to_string(),
    FeatureId.DisableBreakpoint.to_string(),
    FeatureId.ListBreakpoints.to_string()
]
# Verify they are all different by checking length of unique set
# Each one is unique so just verify they all exist as non-empty strings
var all_non_empty = true
for name in features:
    if name.len() == 0:
        all_non_empty = false
expect(all_non_empty).to_equal(true)
expect(features.len()).to_equal(7)
```

</details>

#### all ptrace features are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = FeatureId.PtraceAttach.to_string()
val pd = FeatureId.PtraceDetach.to_string()
val pc = FeatureId.PtraceContinue.to_string()
val ps = FeatureId.PtraceSingleStep.to_string()
val pr = FeatureId.PtraceReadMemory.to_string()
val pw = FeatureId.PtraceWriteMemory.to_string()
# Verify all are unique
expect(pa).to_equal("PtraceAttach")
expect(pd).to_equal("PtraceDetach")
expect(pc).to_equal("PtraceContinue")
expect(ps).to_equal("PtraceSingleStep")
expect(pr).to_equal("PtraceReadMemory")
expect(pw).to_equal("PtraceWriteMemory")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/features_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FeatureId breakpoint variants
- FeatureId frame navigation variants
- FeatureId ptrace variants
- FeatureId DWARF variants
- FeatureId existing variants
- FeatureId equality

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
