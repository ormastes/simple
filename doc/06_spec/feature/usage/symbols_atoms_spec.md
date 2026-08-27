# Symbols and Atoms Specification

> Symbols (also called atoms) are immutable, interned identifiers that are compared by identity rather than value. They provide efficient comparison operations and are commonly used for keys, tags, and enum-like values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbols and Atoms Specification

Symbols (also called atoms) are immutable, interned identifiers that are compared by identity rather than value. They provide efficient comparison operations and are commonly used for keys, tags, and enum-like values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYMBOLS-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/feature/usage/symbols_atoms_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Symbols (also called atoms) are immutable, interned identifiers that are
compared by identity rather than value. They provide efficient comparison
operations and are commonly used for keys, tags, and enum-like values.

## Syntax

```simple
use std.spec.step

val status = :ok
val error = :not_found

if status is :ok:
handle_success()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Symbol | Interned identifier compared by identity |
| Atom | Alternative name for symbol (Erlang terminology) |
| Interning | Process of storing unique string once |
| Symbol Table | Runtime storage for interned symbols |

## Behavior

- Symbols are prefixed with colon: `:name`
- Symbol comparison is O(1) pointer equality
- All occurrences of same symbol share memory
- Symbols are immutable and cannot be modified

## Scenarios

### Symbol Creation

#### creates simple symbol

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates simple symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates simple symbol")
val status = :ok
var result = 0
if status is :ok:
    result = 1
expect result == 1
```

</details>

#### creates symbol with underscore

- creates symbol with underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates symbol with underscore")
val err = :not_found
var result = 0
if err is :not_found:
    result = 1
expect result == 1
```

</details>

#### creates multiple distinct symbols

- creates multiple distinct symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates multiple distinct symbols")
val a = :hello
val b = :world
var result = 0
if a is :hello:
    if b is :world:
        result = 1
expect result == 1
```

</details>

### Symbol Comparison

#### compares equal symbols

- compares equal symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("compares equal symbols")
val a = :hello
val b = :hello
var result = 0
if a is b:
    result = 10
expect result == 10
```

</details>

#### distinguishes different symbols

- distinguishes different symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("distinguishes different symbols")
val a = :hello
val b = :world
var result = 1
if a is b:
    result = 0
expect result == 1
```

</details>

#### compares symbol in if-else

- compares symbol in if-else


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("compares symbol in if-else")
val status = :ok
val result = if status is :ok: 42 else: 0
expect result == 42
```

</details>

#### compares symbol with not equal

- compares symbol with not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("compares symbol with not equal")
val a = :hello
val b = :world
var result = 0
if not (a is b):
    result = 1
expect result == 1
```

</details>

### Symbol Use Cases

#### uses symbol as return value

- uses symbol as return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses symbol as return value")
fn get_status():
    return :success
val result = get_status()
var r = 0
if result is :success:
    r = 1
expect r == 1
```

</details>

#### uses symbol as function parameter

- uses symbol as function parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses symbol as function parameter")
fn process(status):
    if status is :ok:
        return 42
    return 0
expect process(:ok) == 42
```

</details>

#### uses symbol in conditional logic

- uses symbol in conditional logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses symbol in conditional logic")
val state = :running
var code = 0
if state is :stopped:
    code = 1
else:
    if state is :running:
        code = 2
    else:
        code = 3
expect code == 2
```

</details>

#### chains symbol checks

- chains symbol checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains symbol checks")
val a = :first
val b = :second
var result = 0
if a is :first:
    if b is :second:
        result = 100
expect result == 100
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45943a5688907d4447ee4bf8e31cb12b5b096923dcf57ffe303195f60c04b822`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45943a5688907d4447ee4bf8e31cb12b5b096923dcf57ffe303195f60c04b822`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45943a5688907d4447ee4bf8e31cb12b5b096923dcf57ffe303195f60c04b822`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/symbols_atoms_spec.spl
mirror: doc/06_spec/feature/usage/symbols_atoms_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/symbols_atoms_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/symbols_atoms_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/symbols_atoms_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates simple symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/symbols_atoms_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates symbol with underscore' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/symbols_atoms_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates multiple distinct symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
