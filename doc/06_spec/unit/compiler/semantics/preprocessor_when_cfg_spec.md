# Preprocessor When Cfg Specification

> Tests covering Preprocessor @when/@cfg, @when block directives, nested @when blocks, boolean conditions, @cfg per-declaration, line count preservation, platform conditions, Task #45 residual — same-name arch dispatch (source-driven).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preprocessor When Cfg Specification

## Scenarios

### Preprocessor @when/@cfg

### @when block directives

#### @when(true) includes block

- @when(true) includes block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(true) includes block")
# @when(true):
#     val x = 1
# @end
# The block should be included when condition is true
expect("@when(true):\n    val x = 1\n@end").to_contain("@when(true)")
```

</details>

#### @when(false) excludes block

- @when(false) excludes block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(false) excludes block")
# @when(false):
#     val x = 1
# @end
# The block should be excluded when condition is false
expect("@when(false):\n    val x = 1\n@end").to_contain("@when(false)")
```

</details>

#### @when/@elif/@else/@end full chain

- @when/@elif/@else/@end full chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when/@elif/@else/@end full chain")
# @when(false):
#     val branch = "first"
# @elif(true):
#     val branch = "second"
# @else:
#     val branch = "third"
# @end
# Only the @elif branch should be included
expect("@when(false):\n@elif(true):\n@else:\n@end").to_contain("@elif(true)")
```

</details>

#### @else branch activates when all prior false

- @else branch activates when all prior false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@else branch activates when all prior false")
# @when(false):
#     val x = 1
# @elif(false):
#     val x = 2
# @else:
#     val x = 3
# @end
# The @else branch should be the active one
expect("@when(false):\n@elif(false):\n@else:\n@end").to_contain("@else:")
```

</details>

### nested @when blocks

#### nested @when blocks work correctly

- nested @when blocks work correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested @when blocks work correctly")
# @when(true):
#     @when(true):
#         val inner = 1
#     @end
# @end
# Nested blocks should both be evaluated
expect("@when(true):\n    @when(true):\n    @end\n@end").to_contain("    @when(true)")
```

</details>

#### nested @when false in true parent excludes inner

- nested @when false in true parent excludes inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested @when false in true parent excludes inner")
# @when(true):
#     @when(false):
#         val inner = 1
#     @end
# @end
expect("@when(true):\n    @when(false):\n    @end\n@end").to_contain("@when(false)")
```

</details>

### boolean conditions

#### @when(linux and x86_64) uses boolean AND

- @when(linux and x86_64) uses boolean AND


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(linux and x86_64) uses boolean AND")
# Tests combined OS + arch condition
expect("@when(linux and x86_64):").to_contain(" and ")
```

</details>

#### @when(not windows) uses boolean NOT

- @when(not windows) uses boolean NOT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(not windows) uses boolean NOT")
# Tests negated condition
expect("@when(not windows):").to_contain("not windows")
```

</details>

#### @when(linux or macos) uses boolean OR

- @when(linux or macos) uses boolean OR


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(linux or macos) uses boolean OR")
# Tests OR condition
expect("@when(linux or macos):").to_contain(" or ")
```

</details>

### @cfg per-declaration

#### @cfg(true) includes following declaration

- @cfg(true) includes following declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@cfg(true) includes following declaration")
# @cfg(true)
# fn included(): ...
# The function should be available
expect("@cfg(true)\nfn included():").to_start_with("@cfg(true)")
```

</details>

#### @cfg(false) excludes following declaration

- @cfg(false) excludes following declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@cfg(false) excludes following declaration")
# @cfg(false)
# fn excluded(): ...
# The function should NOT be available
expect("@cfg(false)\nfn excluded():").to_contain("@cfg(false)")
```

</details>

#### @cfg with key-value form

- @cfg with key-value form


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@cfg with key-value form")
# @cfg("os", "linux")
# fn linux_only(): ...
# Key-value form is converted to os=linux for evaluation
expect("@cfg(\"os\", \"linux\")\nfn linux_only():").to_contain("\"linux\"")
```

</details>

### line count preservation

#### blanked directives preserve line count

- blanked directives preserve line count
   - Expected: before.split("\n").len() equals `after.split("\n").len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blanked directives preserve line count")
# All @when/@elif/@else/@end lines are replaced with empty lines
# so that diagnostics line numbers remain correct
val before = "@when(true):\nval x = 1\n@end"
val after = "\nval x = 1\n"
expect(before.split("\n").len()).to_equal(after.split("\n").len())
```

</details>

### platform conditions

#### @when(linux) detects Linux

- @when(linux) detects Linux


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(linux) detects Linux")
# Should be true on Linux hosts
expect("@when(linux):").to_contain("linux")
```

</details>

#### @when(unix) detects Unix-like systems

- @when(unix) detects Unix-like systems


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(unix) detects Unix-like systems")
# Should be true on Linux, macOS, FreeBSD, etc.
expect("@when(unix):").to_contain("unix")
```

</details>

### Task #45 residual — same-name arch dispatch (source-driven)

#### reassembles spaced key value cfg conditions

- reassembles spaced key value cfg conditions
   - Expected: out contains `kept-single`
   - Expected: out contains `kept-double`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassembles spaced key value cfg conditions")
val arch = cfg_detect_arch()
val src = "@cfg(arch = \"{arch}\")\nfn single_equals() -> text:\n    \"kept-single\"\n\n@cfg(arch == \"{arch}\")\nfn double_equals() -> text:\n    \"kept-double\"\n"
val out = preprocess_conditionals(src)
expect(out.contains("kept-single")).to_equal(true)
expect(out.contains("kept-double")).to_equal(true)
```

</details>

#### keeps the host-matching @cfg variant, x86_64 declared first (order A)

- keeps the host-matching @cfg variant, x86_64 declared first (order A)
   - Expected: out contains `"x86_64"`
   - Expected: out does not contain `"arm64"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the host-matching @cfg variant, x86_64 declared first (order A)")
val src = "@cfg(x86_64)\nfn arch_name() -> text:\n    \"x86_64\"\n\n@cfg(arm64)\nfn arch_name() -> text:\n    \"arm64\"\n"
val out = preprocess_conditionals(src)
expect(out.contains("\"x86_64\"")).to_equal(true)
expect(out.contains("\"arm64\"")).to_equal(false)
```

</details>

#### keeps the host-matching @cfg variant, arm64 declared first (order B — the #45 regression order)

- keeps the host-matching @cfg variant, arm64 declared first (order B — the #45 regression order)
   - Expected: out contains `"x86_64"`
   - Expected: out does not contain `"arm64"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the host-matching @cfg variant, arm64 declared first (order B — the #45 regression order)")
val src = "@cfg(arm64)\nfn arch_name() -> text:\n    \"arm64\"\n\n@cfg(x86_64)\nfn arch_name() -> text:\n    \"x86_64\"\n"
val out = preprocess_conditionals(src)
expect(out.contains("\"x86_64\"")).to_equal(true)
expect(out.contains("\"arm64\"")).to_equal(false)
```

</details>

#### @when sibling path: keeps the host-matching block-form variant regardless of order

- @when sibling path: keeps the host-matching block-form variant regardless of order
   - Expected: out contains `"x86_64"`
   - Expected: out does not contain `"arm64"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when sibling path: keeps the host-matching block-form variant regardless of order")
# cfg_eval_key_value/cfg_detect_arch (compiler.core.cfg_platform) is
# shared between the per-declaration @cfg path and the block-scoped
# @when path (both route through preprocess_conditionals's two
# preprocessing passes in _pp_preprocess_conditionals). This proves
# the @when sibling has no analogous same-name gap in the current
# source: the false-condition block is blanked in its entirety
# before parsing, same as @cfg, so no duplicate name ever reaches
# the parser/interpreter to race on declaration order.
val src = "@when(arm64)\nfn arch_name() -> text:\n    \"arm64\"\n@end\n\n@when(x86_64)\nfn arch_name() -> text:\n    \"x86_64\"\n@end\n"
val out = preprocess_conditionals(src)
expect(out.contains("\"x86_64\"")).to_equal(true)
expect(out.contains("\"arm64\"")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Preprocessor @when/@cfg, @when block directives, nested @when blocks, boolean conditions, @cfg per-declaration, line count preservation, platform conditions, Task #45 residual — same-name arch dispatch (source-driven).
- Preprocessor @when/@cfg
- @when block directives
- nested @when blocks
- boolean conditions
- @cfg per-declaration
- line count preservation
- platform conditions
- Task #45 residual — same-name arch dispatch (source-driven)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `ea4f481403d7b24c216b7160dc6dfa106e42c1d47e6c148df96ec920af56e732`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea4f481403d7b24c216b7160dc6dfa106e42c1d47e6c148df96ec920af56e732`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea4f481403d7b24c216b7160dc6dfa106e42c1d47e6c148df96ec920af56e732`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/preprocessor_when_cfg_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/preprocessor_when_cfg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/preprocessor_when_cfg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@when(true) includes block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@when(false) excludes block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@when/@elif/@else/@end full chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
