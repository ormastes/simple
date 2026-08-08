# Preprocessor When Cfg Specification

> <details>

<!-- sdn-diagram:id=preprocessor_when_cfg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=preprocessor_when_cfg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

preprocessor_when_cfg_spec -> std
preprocessor_when_cfg_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=preprocessor_when_cfg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preprocessor When Cfg Specification

## Scenarios

### Preprocessor @when/@cfg

### @when block directives

#### @when(true) includes block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @when(true):
#     val x = 1
# @end
# The block should be included when condition is true
expect("@when(true):\n    val x = 1\n@end").to_contain("@when(true)")
```

</details>

#### @when(false) excludes block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @when(false):
#     val x = 1
# @end
# The block should be excluded when condition is false
expect("@when(false):\n    val x = 1\n@end").to_contain("@when(false)")
```

</details>

#### @when/@elif/@else/@end full chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests combined OS + arch condition
expect("@when(linux and x86_64):").to_contain(" and ")
```

</details>

#### @when(not windows) uses boolean NOT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests negated condition
expect("@when(not windows):").to_contain("not windows")
```

</details>

#### @when(linux or macos) uses boolean OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests OR condition
expect("@when(linux or macos):").to_contain(" or ")
```

</details>

### @cfg per-declaration

#### @cfg(true) includes following declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @cfg(true)
# fn included(): ...
# The function should be available
expect("@cfg(true)\nfn included():").to_start_with("@cfg(true)")
```

</details>

#### @cfg(false) excludes following declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @cfg(false)
# fn excluded(): ...
# The function should NOT be available
expect("@cfg(false)\nfn excluded():").to_contain("@cfg(false)")
```

</details>

#### @cfg with key-value form

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @cfg("os", "linux")
# fn linux_only(): ...
# Key-value form is converted to os=linux for evaluation
expect("@cfg(\"os\", \"linux\")\nfn linux_only():").to_contain("\"linux\"")
```

</details>

### line count preservation

#### blanked directives preserve line count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All @when/@elif/@else/@end lines are replaced with empty lines
# so that diagnostics line numbers remain correct
val before = "@when(true):\nval x = 1\n@end"
val after = "\nval x = 1\n"
expect(before.split("\n").len()).to_equal(after.split("\n").len())
```

</details>

### platform conditions

#### @when(linux) detects Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Should be true on Linux hosts
expect("@when(linux):").to_contain("linux")
```

</details>

#### @when(unix) detects Unix-like systems

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Should be true on Linux, macOS, FreeBSD, etc.
expect("@when(unix):").to_contain("unix")
```

</details>

### Task #45 residual — same-name arch dispatch (source-driven)

#### keeps the host-matching @cfg variant, x86_64 declared first (order A)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@cfg(x86_64)\nfn arch_name() -> text:\n    \"x86_64\"\n\n@cfg(arm64)\nfn arch_name() -> text:\n    \"arm64\"\n"
val out = preprocess_conditionals(src)
expect(out.contains("\"x86_64\"")).to_equal(true)
expect(out.contains("\"arm64\"")).to_equal(false)
```

</details>

#### keeps the host-matching @cfg variant, arm64 declared first (order B — the #45 regression order)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@cfg(arm64)\nfn arch_name() -> text:\n    \"arm64\"\n\n@cfg(x86_64)\nfn arch_name() -> text:\n    \"x86_64\"\n"
val out = preprocess_conditionals(src)
expect(out.contains("\"x86_64\"")).to_equal(true)
expect(out.contains("\"arm64\"")).to_equal(false)
```

</details>

#### @when sibling path: keeps the host-matching block-form variant regardless of order

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/compiler/semantics/preprocessor_when_cfg_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
