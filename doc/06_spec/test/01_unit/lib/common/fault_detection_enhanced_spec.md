# Fault Detection Enhanced Specification

> <details>

<!-- sdn-diagram:id=fault_detection_enhanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fault_detection_enhanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fault_detection_enhanced_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fault_detection_enhanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fault Detection Enhanced Specification

## Scenarios

### Enhanced Fault Detection

#### signal fault

#### not detected initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_signal_detected).to_equal(false)
```

</details>

#### set marks active

1. clear all
2. set signal
   - Expected: _signal_detected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_signal(11, "SIGSEGV")
expect(_signal_detected).to_equal(true)
```

</details>

#### stores signal number

1. clear all
2. set signal
   - Expected: _signal_number equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_signal(6, "SIGABRT")
expect(_signal_number).to_equal(6)
```

</details>

#### stores signal name

1. clear all
2. set signal
   - Expected: _signal_name equals `SIGABRT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_signal(6, "SIGABRT")
expect(_signal_name).to_equal("SIGABRT")
```

</details>

#### clear resets

1. clear all
2. set signal
3. clear signal
   - Expected: _signal_detected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_signal(11, "SIGSEGV")
clear_signal()
expect(_signal_detected).to_equal(false)
```

</details>

#### memory exceeded

#### not exceeded initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_memory_exceeded).to_equal(false)
```

</details>

#### set marks active

1. clear all
2. set memory
   - Expected: _memory_exceeded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_memory(512, 256)
expect(_memory_exceeded).to_equal(true)
```

</details>

#### stores used and limit

1. clear all
2. set memory
   - Expected: _memory_used equals `512`
   - Expected: _memory_limit equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_memory(512, 256)
expect(_memory_used).to_equal(512)
expect(_memory_limit).to_equal(256)
```

</details>

#### clear resets

1. clear all
2. set memory
3. clear memory
   - Expected: _memory_exceeded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_memory(512, 256)
clear_memory()
expect(_memory_exceeded).to_equal(false)
```

</details>

#### interrupt

#### not requested initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_interrupt).to_equal(false)
```

</details>

#### set marks active

1. clear all
2. set interrupt
   - Expected: _interrupt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_interrupt()
expect(_interrupt).to_equal(true)
```

</details>

#### fault priority

#### signal highest

1. clear all
2. set signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_signal(11, "SIGSEGV")
_timeout = true
_interrupt = true
expect(check()).to_start_with("signal:")
```

</details>

#### memory over timeout

1. clear all
2. set memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
set_memory(512, 256)
_timeout = true
expect(check()).to_start_with("memory:")
```

</details>

#### timeout over stack overflow

1. clear all
   - Expected: check() equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
_timeout = true
_recursion_depth = 2000
expect(check()).to_equal("timeout")
```

</details>

#### stack overflow over interrupt

1. clear all


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
_recursion_depth = 2000
_interrupt = true
expect(check()).to_start_with("stack_overflow:")
```

</details>

#### interrupt lowest

1. clear all
   - Expected: check() equals `interrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
_interrupt = true
expect(check()).to_equal("interrupt")
```

</details>

#### no fault returns empty

1. clear all
   - Expected: check() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
expect(check()).to_equal("")
```

</details>

#### reset

#### clears all state

1. set signal
2. set memory
3. set interrupt
4. clear all
   - Expected: check() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_signal(11, "SIGSEGV")
set_memory(512, 256)
set_interrupt()
_timeout = true
clear_all()
expect(check()).to_equal("")
```

</details>

#### restores defaults

1. clear all
   - Expected: _max_depth equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_all()
expect(_max_depth).to_equal(1000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/fault_detection_enhanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Enhanced Fault Detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
