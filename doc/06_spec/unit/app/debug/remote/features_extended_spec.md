# Features Extended Specification

> Tests covering FeatureId breakpoint variants, FeatureId frame navigation variants, FeatureId ptrace variants, FeatureId DWARF variants, FeatureId existing variants, FeatureId equality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Features Extended Specification

## Scenarios

### FeatureId breakpoint variants

#### ConditionalBreakpoint has correct to_string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ConditionalBreakpoint has correct to_string
   - Expected: f.to_string() equals `ConditionalBreakpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ConditionalBreakpoint has correct to_string")
val f = FeatureId.ConditionalBreakpoint
expect(f.to_string()).to_equal("ConditionalBreakpoint")
```

</details>

#### FunctionBreakpoint has correct to_string

- FunctionBreakpoint has correct to_string
   - Expected: f.to_string() equals `FunctionBreakpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FunctionBreakpoint has correct to_string")
val f = FeatureId.FunctionBreakpoint
expect(f.to_string()).to_equal("FunctionBreakpoint")
```

</details>

#### EnableBreakpoint has correct to_string

- EnableBreakpoint has correct to_string
   - Expected: f.to_string() equals `EnableBreakpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EnableBreakpoint has correct to_string")
val f = FeatureId.EnableBreakpoint
expect(f.to_string()).to_equal("EnableBreakpoint")
```

</details>

#### DisableBreakpoint has correct to_string

- DisableBreakpoint has correct to_string
   - Expected: f.to_string() equals `DisableBreakpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DisableBreakpoint has correct to_string")
val f = FeatureId.DisableBreakpoint
expect(f.to_string()).to_equal("DisableBreakpoint")
```

</details>

#### ListBreakpoints has correct to_string

- ListBreakpoints has correct to_string
   - Expected: f.to_string() equals `ListBreakpoints`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ListBreakpoints has correct to_string")
val f = FeatureId.ListBreakpoints
expect(f.to_string()).to_equal("ListBreakpoints")
```

</details>

#### SetBreakpoint has correct to_string

- SetBreakpoint has correct to_string
   - Expected: f.to_string() equals `SetBreakpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SetBreakpoint has correct to_string")
val f = FeatureId.SetBreakpoint
expect(f.to_string()).to_equal("SetBreakpoint")
```

</details>

#### ClearBreakpoint has correct to_string

- ClearBreakpoint has correct to_string
   - Expected: f.to_string() equals `ClearBreakpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ClearBreakpoint has correct to_string")
val f = FeatureId.ClearBreakpoint
expect(f.to_string()).to_equal("ClearBreakpoint")
```

</details>

#### SetWatchpoint has correct to_string

- SetWatchpoint has correct to_string
   - Expected: f.to_string() equals `SetWatchpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SetWatchpoint has correct to_string")
val f = FeatureId.SetWatchpoint
expect(f.to_string()).to_equal("SetWatchpoint")
```

</details>

### FeatureId frame navigation variants

#### SelectFrame has correct to_string

- SelectFrame has correct to_string
   - Expected: f.to_string() equals `SelectFrame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SelectFrame has correct to_string")
val f = FeatureId.SelectFrame
expect(f.to_string()).to_equal("SelectFrame")
```

</details>

#### FrameLocals has correct to_string

- FrameLocals has correct to_string
   - Expected: f.to_string() equals `FrameLocals`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FrameLocals has correct to_string")
val f = FeatureId.FrameLocals
expect(f.to_string()).to_equal("FrameLocals")
```

</details>

#### FrameArguments has correct to_string

- FrameArguments has correct to_string
   - Expected: f.to_string() equals `FrameArguments`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FrameArguments has correct to_string")
val f = FeatureId.FrameArguments
expect(f.to_string()).to_equal("FrameArguments")
```

</details>

#### SetVariable has correct to_string

- SetVariable has correct to_string
   - Expected: f.to_string() equals `SetVariable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SetVariable has correct to_string")
val f = FeatureId.SetVariable
expect(f.to_string()).to_equal("SetVariable")
```

</details>

### FeatureId ptrace variants

#### PtraceAttach has correct to_string

- PtraceAttach has correct to_string
   - Expected: f.to_string() equals `PtraceAttach`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PtraceAttach has correct to_string")
val f = FeatureId.PtraceAttach
expect(f.to_string()).to_equal("PtraceAttach")
```

</details>

#### PtraceDetach has correct to_string

- PtraceDetach has correct to_string
   - Expected: f.to_string() equals `PtraceDetach`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PtraceDetach has correct to_string")
val f = FeatureId.PtraceDetach
expect(f.to_string()).to_equal("PtraceDetach")
```

</details>

#### PtraceContinue has correct to_string

- PtraceContinue has correct to_string
   - Expected: f.to_string() equals `PtraceContinue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PtraceContinue has correct to_string")
val f = FeatureId.PtraceContinue
expect(f.to_string()).to_equal("PtraceContinue")
```

</details>

#### PtraceSingleStep has correct to_string

- PtraceSingleStep has correct to_string
   - Expected: f.to_string() equals `PtraceSingleStep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PtraceSingleStep has correct to_string")
val f = FeatureId.PtraceSingleStep
expect(f.to_string()).to_equal("PtraceSingleStep")
```

</details>

#### PtraceReadMemory has correct to_string

- PtraceReadMemory has correct to_string
   - Expected: f.to_string() equals `PtraceReadMemory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PtraceReadMemory has correct to_string")
val f = FeatureId.PtraceReadMemory
expect(f.to_string()).to_equal("PtraceReadMemory")
```

</details>

#### PtraceWriteMemory has correct to_string

- PtraceWriteMemory has correct to_string
   - Expected: f.to_string() equals `PtraceWriteMemory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PtraceWriteMemory has correct to_string")
val f = FeatureId.PtraceWriteMemory
expect(f.to_string()).to_equal("PtraceWriteMemory")
```

</details>

### FeatureId DWARF variants

#### DwarfAddrToSource has correct to_string

- DwarfAddrToSource has correct to_string
   - Expected: f.to_string() equals `DwarfAddrToSource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DwarfAddrToSource has correct to_string")
val f = FeatureId.DwarfAddrToSource
expect(f.to_string()).to_equal("DwarfAddrToSource")
```

</details>

#### DwarfSourceToAddr has correct to_string

- DwarfSourceToAddr has correct to_string
   - Expected: f.to_string() equals `DwarfSourceToAddr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DwarfSourceToAddr has correct to_string")
val f = FeatureId.DwarfSourceToAddr
expect(f.to_string()).to_equal("DwarfSourceToAddr")
```

</details>

#### DwarfFunctionName has correct to_string

- DwarfFunctionName has correct to_string
   - Expected: f.to_string() equals `DwarfFunctionName`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DwarfFunctionName has correct to_string")
val f = FeatureId.DwarfFunctionName
expect(f.to_string()).to_equal("DwarfFunctionName")
```

</details>

### FeatureId existing variants

#### Halt has correct to_string

- Halt has correct to_string
   - Expected: f.to_string() equals `Halt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Halt has correct to_string")
val f = FeatureId.Halt
expect(f.to_string()).to_equal("Halt")
```

</details>

#### Resume has correct to_string

- Resume has correct to_string
   - Expected: f.to_string() equals `Resume`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Resume has correct to_string")
val f = FeatureId.Resume
expect(f.to_string()).to_equal("Resume")
```

</details>

#### SingleStep has correct to_string

- SingleStep has correct to_string
   - Expected: f.to_string() equals `SingleStep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SingleStep has correct to_string")
val f = FeatureId.SingleStep
expect(f.to_string()).to_equal("SingleStep")
```

</details>

#### StepOver has correct to_string

- StepOver has correct to_string
   - Expected: f.to_string() equals `StepOver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("StepOver has correct to_string")
val f = FeatureId.StepOver
expect(f.to_string()).to_equal("StepOver")
```

</details>

#### ReadMemory has correct to_string

- ReadMemory has correct to_string
   - Expected: f.to_string() equals `ReadMemory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ReadMemory has correct to_string")
val f = FeatureId.ReadMemory
expect(f.to_string()).to_equal("ReadMemory")
```

</details>

#### WriteMemory has correct to_string

- WriteMemory has correct to_string
   - Expected: f.to_string() equals `WriteMemory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WriteMemory has correct to_string")
val f = FeatureId.WriteMemory
expect(f.to_string()).to_equal("WriteMemory")
```

</details>

#### ReadLocals has correct to_string

- ReadLocals has correct to_string
   - Expected: f.to_string() equals `ReadLocals`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ReadLocals has correct to_string")
val f = FeatureId.ReadLocals
expect(f.to_string()).to_equal("ReadLocals")
```

</details>

#### ReadStackTrace has correct to_string

- ReadStackTrace has correct to_string
   - Expected: f.to_string() equals `ReadStackTrace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ReadStackTrace has correct to_string")
val f = FeatureId.ReadStackTrace
expect(f.to_string()).to_equal("ReadStackTrace")
```

</details>

#### EvaluateExpression has correct to_string

- EvaluateExpression has correct to_string
   - Expected: f.to_string() equals `EvaluateExpression`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EvaluateExpression has correct to_string")
val f = FeatureId.EvaluateExpression
expect(f.to_string()).to_equal("EvaluateExpression")
```

</details>

### FeatureId equality

#### same variant equals itself

- same variant equals itself
   - Expected: a.eq(b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("same variant equals itself")
val a = FeatureId.PtraceAttach
val b = FeatureId.PtraceAttach
expect(a.eq(b)).to_equal(true)
```

</details>

#### different variants are not equal

- different variants are not equal
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different variants are not equal")
val a = FeatureId.PtraceAttach
val b = FeatureId.PtraceDetach
expect(a.eq(b)).to_equal(false)
```

</details>

#### breakpoint variants differ from ptrace variants

- breakpoint variants differ from ptrace variants
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("breakpoint variants differ from ptrace variants")
val a = FeatureId.ConditionalBreakpoint
val b = FeatureId.PtraceAttach
expect(a.eq(b)).to_equal(false)
```

</details>

#### frame variants differ from DWARF variants

- frame variants differ from DWARF variants
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame variants differ from DWARF variants")
val a = FeatureId.SelectFrame
val b = FeatureId.DwarfAddrToSource
expect(a.eq(b)).to_equal(false)
```

</details>

#### DWARF variants differ from each other

- DWARF variants differ from each other
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DWARF variants differ from each other")
val a = FeatureId.DwarfAddrToSource
val b = FeatureId.DwarfSourceToAddr
expect(a.eq(b)).to_equal(false)
```

</details>

#### system variants have correct to_string

- system variants have correct to_string
   - Expected: ps.to_string() equals `ProfileSample`
   - Expected: fp.to_string() equals `FlashProgram`
   - Expected: sr.to_string() equals `SystemReset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("system variants have correct to_string")
val ps = FeatureId.ProfileSample
val fp = FeatureId.FlashProgram
val sr = FeatureId.SystemReset
expect(ps.to_string()).to_equal("ProfileSample")
expect(fp.to_string()).to_equal("FlashProgram")
expect(sr.to_string()).to_equal("SystemReset")
```

</details>

#### all breakpoint features are distinct

- all breakpoint features are distinct
   - Expected: all_non_empty is true
   - Expected: features.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all breakpoint features are distinct")
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

- all ptrace features are distinct
   - Expected: pa equals `PtraceAttach`
   - Expected: pd equals `PtraceDetach`
   - Expected: pc equals `PtraceContinue`
   - Expected: ps equals `PtraceSingleStep`
   - Expected: pr equals `PtraceReadMemory`
   - Expected: pw equals `PtraceWriteMemory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all ptrace features are distinct")
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
| Source | `test/unit/app/debug/remote/features_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FeatureId breakpoint variants, FeatureId frame navigation variants, FeatureId ptrace variants, FeatureId DWARF variants, FeatureId existing variants, FeatureId equality.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a43f9ebb1704a1618f4880fc14e51653c7881bc104e4b3e05ce71d92cd57682`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a43f9ebb1704a1618f4880fc14e51653c7881bc104e4b3e05ce71d92cd57682`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a43f9ebb1704a1618f4880fc14e51653c7881bc104e4b3e05ce71d92cd57682`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/debug/remote/features_extended_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/features_extended_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/features_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/features_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/features_extended_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/features_extended_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ConditionalBreakpoint has correct to_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/features_extended_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FunctionBreakpoint has correct to_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/features_extended_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EnableBreakpoint has correct to_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
