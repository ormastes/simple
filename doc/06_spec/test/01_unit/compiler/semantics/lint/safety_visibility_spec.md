# Safety Visibility Specification

> <details>

<!-- sdn-diagram:id=safety_visibility_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=safety_visibility_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

safety_visibility_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=safety_visibility_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safety Visibility Specification

## Scenarios

### Safety and Visibility Lint

#### private symbol imports

#### flags importing _private_fn from another module (W0401)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.nogc_sync_mut.fs.{_private_helper}' + "\n\nfn test():\n    print \"test\"\n"
val codes = check_visibility_text(code)
val has_w0401 = codes_contain(codes, "W0401")
expect(has_w0401).to_equal(true)
```

</details>

#### flags importing _internal symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.common.text.{_internal_parse}' + "\n\nfn test():\n    print \"test\"\n"
val codes = check_visibility_text(code)
val has_w0401 = codes_contain(codes, "W0401")
expect(has_w0401).to_equal(true)
```

</details>

#### public symbol imports

#### does not flag importing public symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use std.spec\n\nfn test():\n    print \"test\"\n"
val codes = check_visibility_text(code)
val has_w0401 = codes_contain(codes, "W0401")
expect(has_w0401).to_equal(false)
```

</details>

#### asm outside unsafe

#### flags asm usage outside unsafe block (SAFE001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    asm \"nop\"\n"
val codes = check_safety_text(code)
val has_safe001 = codes_contain(codes, "SAFE001")
expect(has_safe001).to_equal(true)
```

</details>

#### flags standalone asm on indented line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn compute():\n    asm \"mov eax, 42\"\n    print \"done\"\n"
val codes = check_safety_text(code)
val has_safe001 = codes_contain(codes, "SAFE001")
expect(has_safe001).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/safety_visibility_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Safety and Visibility Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
