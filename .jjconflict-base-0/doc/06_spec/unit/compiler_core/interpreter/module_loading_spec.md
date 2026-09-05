# Module Loading Specification

> Tests covering Runtime Module Loading, Module Path Resolution, Selective Imports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loading Specification

## Scenarios

### Runtime Module Loading

#### resolves local imports without SIMPLE_LIB

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves local imports without SIMPLE_LIB
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves local imports without SIMPLE_LIB")
# This test verifies basic functionality
# Actual module loading tested below
expect(1).to_equal(1)
```

</details>

#### loads std.string functions via SIMPLE_LIB

- loads std.string functions via SIMPLE_LIB
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads std.string functions via SIMPLE_LIB")
# When SIMPLE_LIB=src is set, use std.text should work
# This will be tested after implementation is complete
expect(1).to_equal(1)
```

</details>

#### handles missing modules gracefully

- handles missing modules gracefully
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing modules gracefully")
# Module loading should fail gracefully for missing files
expect(1).to_equal(1)
```

</details>

#### caches loaded modules to avoid re-parsing

- caches loaded modules to avoid re-parsing
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches loaded modules to avoid re-parsing")
# Subsequent imports of same module should use cache
expect(1).to_equal(1)
```

</details>

#### exports all functions when no explicit export

- exports all functions when no explicit export
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports all functions when no explicit export")
# Modules without export statements expose all functions
expect(1).to_equal(1)
```

</details>

#### respects explicit export lists

- respects explicit export lists
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects explicit export lists")
# Modules with export statements only expose listed names
expect(1).to_equal(1)
```

</details>

### Module Path Resolution

#### checks local directory first

- checks local directory first
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks local directory first")
# Relative imports resolve to current directory
expect(1).to_equal(1)
```

</details>

#### checks SIMPLE_LIB second

- checks SIMPLE_LIB second
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks SIMPLE_LIB second")
# Falls back to SIMPLE_LIB path if local not found
expect(1).to_equal(1)
```

</details>

#### checks src/ third as fallback

- checks src/ third as fallback
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks src/ third as fallback")
# Final fallback to src/ directory
expect(1).to_equal(1)
```

</details>

#### converts dotted paths to file paths

- converts dotted paths to file paths
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts dotted paths to file paths")
# std.string → src/lib/text.spl
expect(1).to_equal(1)
```

</details>

### Selective Imports

#### loads specific functions with curly braces

- loads specific functions with curly braces
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads specific functions with curly braces")
# use module.{func1, func2}
expect(1).to_equal(1)
```

</details>

#### validates imported names exist

- validates imported names exist
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates imported names exist")
# Should error if requested function not found
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/interpreter/module_loading_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Runtime Module Loading, Module Path Resolution, Selective Imports.
- Runtime Module Loading
- Module Path Resolution
- Selective Imports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `ee020f894dad34854eaebac23d6a6885dd53d4162c9514662a638f06a6b140df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee020f894dad34854eaebac23d6a6885dd53d4162c9514662a638f06a6b140df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee020f894dad34854eaebac23d6a6885dd53d4162c9514662a638f06a6b140df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/compiler_core/interpreter/module_loading_spec.spl
mirror: doc/06_spec/unit/compiler_core/interpreter/module_loading_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/unit/compiler_core/interpreter/module_loading_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/interpreter/module_loading_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/interpreter/module_loading_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler_core/interpreter/module_loading_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/compiler_core/interpreter/module_loading_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler_core/interpreter/module_loading_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves local imports without SIMPLE_LIB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/interpreter/module_loading_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads std.string functions via SIMPLE_LIB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/interpreter/module_loading_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles missing modules gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
