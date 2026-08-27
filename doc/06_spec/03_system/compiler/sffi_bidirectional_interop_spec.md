# Sffi Bidirectional Interop Specification

> Tests covering SFFI Bidirectional Class Interop.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sffi Bidirectional Interop Specification

## Scenarios

### SFFI Bidirectional Class Interop

#### fixture declares C representation and C export

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fixture declares C representation and C export


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture declares C representation and C export")
val source = sffi_fixture_source()
expect(source).to_contain("@repr(\"C\")")
expect(source).to_contain("@export(\"C\")")
expect(source).to_contain("class GpioRegister")
```

</details>

#### fixture carries bitfield metadata expected by C layout generation

- fixture carries bitfield metadata expected by C layout generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture carries bitfield metadata expected by C layout generation")
val source = sffi_fixture_source()
expect(source).to_contain("mode: u8 @bits(4)")
expect(source).to_contain("output: bool @bits(1)")
expect(source).to_contain("input: bool @bits(1)")
expect(source).to_contain("speed: u8 @bits(2)")
```

</details>

#### fixture includes standalone exported function

- fixture includes standalone exported function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture includes standalone exported function")
val source = sffi_fixture_source()
expect(source).to_contain("fn add_numbers(a: i32, b: i32) -> i32")
expect(source).to_contain("a + b")
```

</details>

#### shared library naming follows supported platform conventions

- shared library naming follows supported platform conventions
   - Expected: shared_lib_name("gpio_driver", "linux") equals `libgpio_driver.so`
   - Expected: shared_lib_name("gpio_driver", "darwin") equals `libgpio_driver.dylib`
   - Expected: shared_lib_name("gpio_driver", "windows") equals `gpio_driver.dll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shared library naming follows supported platform conventions")
expect(shared_lib_name("gpio_driver", "linux")).to_equal("libgpio_driver.so")
expect(shared_lib_name("gpio_driver", "darwin")).to_equal("libgpio_driver.dylib")
expect(shared_lib_name("gpio_driver", "windows")).to_equal("gpio_driver.dll")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/sffi_bidirectional_interop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SFFI Bidirectional Class Interop.
- SFFI Bidirectional Class Interop

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3b5d58bae808466a92db5994954350aefbc9df280c0c1f8aed553a4baf16c8a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3b5d58bae808466a92db5994954350aefbc9df280c0c1f8aed553a4baf16c8a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3b5d58bae808466a92db5994954350aefbc9df280c0c1f8aed553a4baf16c8a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/sffi_bidirectional_interop_spec.spl
mirror: doc/06_spec/03_system/compiler/sffi_bidirectional_interop_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/sffi_bidirectional_interop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/sffi_bidirectional_interop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/sffi_bidirectional_interop_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture declares C representation and C export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/sffi_bidirectional_interop_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture carries bitfield metadata expected by C layout generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/sffi_bidirectional_interop_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture includes standalone exported function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
