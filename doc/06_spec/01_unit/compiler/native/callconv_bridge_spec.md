# Callconv Bridge Specification

> Tests covering callconv_bridge, callconv_from_string, callconv_resolve_from_flags, callconv_needs_prologue, callconv_is_interrupt_compat.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Callconv Bridge Specification

## Scenarios

### callconv_bridge

### callconv_from_string

#### maps C to C convention

- maps C to C convention
   - Expected: result equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps C to C convention")
val result = spec_callconv_from_string("C")
expect(result).to_equal("C")
```

</details>

#### maps Fastcall to Fastcall convention

- maps Fastcall to Fastcall convention
   - Expected: result equals `Fastcall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Fastcall to Fastcall convention")
val result = spec_callconv_from_string("Fastcall")
expect(result).to_equal("Fastcall")
```

</details>

#### maps Stdcall to Stdcall convention

- maps Stdcall to Stdcall convention
   - Expected: result equals `Stdcall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Stdcall to Stdcall convention")
val result = spec_callconv_from_string("Stdcall")
expect(result).to_equal("Stdcall")
```

</details>

#### maps Vectorcall to Vectorcall convention

- maps Vectorcall to Vectorcall convention
   - Expected: result equals `Vectorcall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Vectorcall to Vectorcall convention")
val result = spec_callconv_from_string("Vectorcall")
expect(result).to_equal("Vectorcall")
```

</details>

#### maps Naked to Naked convention

- maps Naked to Naked convention
   - Expected: result equals `Naked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Naked to Naked convention")
val result = spec_callconv_from_string("Naked")
expect(result).to_equal("Naked")
```

</details>

#### maps Interrupt to Interrupt convention

- maps Interrupt to Interrupt convention
   - Expected: result equals `Interrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Interrupt to Interrupt convention")
val result = spec_callconv_from_string("Interrupt")
expect(result).to_equal("Interrupt")
```

</details>

#### maps unknown string to Simple fallback

- maps unknown string to Simple fallback
   - Expected: result equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps unknown string to Simple fallback")
val result = spec_callconv_from_string("UnknownABI")
expect(result).to_equal("Simple")
```

</details>

### callconv_resolve_from_flags

#### naked flag resolves to Naked when no explicit callconv

- naked flag resolves to Naked when no explicit callconv
   - Expected: result equals `Naked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("naked flag resolves to Naked when no explicit callconv")
val result = spec_callconv_resolve_from_flags(true, false, false, "")
expect(result).to_equal("Naked")
```

</details>

#### interrupt flag resolves to Interrupt when no explicit callconv

- interrupt flag resolves to Interrupt when no explicit callconv
   - Expected: result equals `Interrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interrupt flag resolves to Interrupt when no explicit callconv")
val result = spec_callconv_resolve_from_flags(false, true, false, "")
expect(result).to_equal("Interrupt")
```

</details>

#### explicit callconv C overrides naked flag

- explicit callconv C overrides naked flag
   - Expected: result equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit callconv C overrides naked flag")
val result = spec_callconv_resolve_from_flags(true, false, true, "C")
expect(result).to_equal("C")
```

</details>

#### explicit callconv Fastcall overrides interrupt flag

- explicit callconv Fastcall overrides interrupt flag
   - Expected: result equals `Fastcall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit callconv Fastcall overrides interrupt flag")
val result = spec_callconv_resolve_from_flags(false, true, true, "Fastcall")
expect(result).to_equal("Fastcall")
```

</details>

#### no flags resolves to Simple default

- no flags resolves to Simple default
   - Expected: result equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no flags resolves to Simple default")
val result = spec_callconv_resolve_from_flags(false, false, false, "")
expect(result).to_equal("Simple")
```

</details>

### callconv_needs_prologue

#### Naked convention does not need prologue

- Naked convention does not need prologue
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Naked convention does not need prologue")
val result = spec_callconv_needs_prologue("Naked")
expect(result).to_equal(false)
```

</details>

#### C convention needs prologue

- C convention needs prologue
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C convention needs prologue")
val result = spec_callconv_needs_prologue("C")
expect(result).to_equal(true)
```

</details>

#### Simple convention needs prologue

- Simple convention needs prologue
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Simple convention needs prologue")
val result = spec_callconv_needs_prologue("Simple")
expect(result).to_equal(true)
```

</details>

#### Interrupt convention needs prologue

- Interrupt convention needs prologue
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Interrupt convention needs prologue")
val result = spec_callconv_needs_prologue("Interrupt")
expect(result).to_equal(true)
```

</details>

### callconv_is_interrupt_compat

#### Interrupt convention is interrupt compatible

- Interrupt convention is interrupt compatible
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Interrupt convention is interrupt compatible")
val result = spec_callconv_is_interrupt_compat("Interrupt")
expect(result).to_equal(true)
```

</details>

#### Naked convention is interrupt compatible

- Naked convention is interrupt compatible
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Naked convention is interrupt compatible")
val result = spec_callconv_is_interrupt_compat("Naked")
expect(result).to_equal(true)
```

</details>

#### C convention is not interrupt compatible

- C convention is not interrupt compatible
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C convention is not interrupt compatible")
val result = spec_callconv_is_interrupt_compat("C")
expect(result).to_equal(false)
```

</details>

#### Simple convention is not interrupt compatible

- Simple convention is not interrupt compatible
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Simple convention is not interrupt compatible")
val result = spec_callconv_is_interrupt_compat("Simple")
expect(result).to_equal(false)
```

</details>

#### Fastcall convention is not interrupt compatible

- Fastcall convention is not interrupt compatible
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Fastcall convention is not interrupt compatible")
val result = spec_callconv_is_interrupt_compat("Fastcall")
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/callconv_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering callconv_bridge, callconv_from_string, callconv_resolve_from_flags, callconv_needs_prologue, callconv_is_interrupt_compat.
- callconv_bridge
- callconv_from_string
- callconv_resolve_from_flags
- callconv_needs_prologue
- callconv_is_interrupt_compat

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `f05b87740ee4983682ea74f9c8184a32b9b55159002b5e0f76e8d17797ff12db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f05b87740ee4983682ea74f9c8184a32b9b55159002b5e0f76e8d17797ff12db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f05b87740ee4983682ea74f9c8184a32b9b55159002b5e0f76e8d17797ff12db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/native/callconv_bridge_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/callconv_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/callconv_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/callconv_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/callconv_bridge_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps C to C convention' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/callconv_bridge_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps Fastcall to Fastcall convention' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/callconv_bridge_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps Stdcall to Stdcall convention' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
