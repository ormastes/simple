# Code Action Kind Specification

> <details>

<!-- sdn-diagram:id=code_action_kind_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=code_action_kind_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

code_action_kind_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=code_action_kind_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Code Action Kind Specification

## Scenarios

### CodeActionKind to_string

#### converts QuickFix to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case QuickFix: "quickfix"
val kind = "quickfix"
expect(kind == "quickfix")
```

</details>

#### converts Refactor to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Refactor: "refactor"
val kind = "refactor"
expect(kind == "refactor")
```

</details>

#### converts RefactorExtract to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorExtract: "refactor.extract"
val kind = "refactor.extract"
expect(kind == "refactor.extract")
```

</details>

#### converts RefactorInline to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorInline: "refactor.inline"
val kind = "refactor.inline"
expect(kind == "refactor.inline")
```

</details>

#### converts RefactorRewrite to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorRewrite: "refactor.rewrite"
val kind = "refactor.rewrite"
expect(kind == "refactor.rewrite")
```

</details>

#### converts Source to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Source: "source"
val kind = "source"
expect(kind == "source")
```

</details>

#### converts SourceOrganizeImports to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case SourceOrganizeImports: "source.organizeImports"
val kind = "source.organizeImports"
expect(kind == "source.organizeImports")
```

</details>

### CodeActionKind description

#### describes QuickFix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case QuickFix: "Quick fix for errors/warnings"
val desc = "Quick fix for errors/warnings"
expect(desc == "Quick fix for errors/warnings")
```

</details>

#### describes Refactor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Refactor: "General refactoring"
val desc = "General refactoring"
expect(desc == "General refactoring")
```

</details>

#### describes RefactorExtract

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorExtract: "Extract code to new element"
val desc = "Extract code to new element"
expect(desc == "Extract code to new element")
```

</details>

#### describes RefactorInline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorInline: "Inline code"
val desc = "Inline code"
expect(desc == "Inline code")
```

</details>

#### describes RefactorRewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorRewrite: "Rewrite code structure"
val desc = "Rewrite code structure"
expect(desc == "Rewrite code structure")
```

</details>

#### describes Source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Source: "Source code action"
val desc = "Source code action"
expect(desc == "Source code action")
```

</details>

#### describes SourceOrganizeImports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case SourceOrganizeImports: "Organize/sort imports"
val desc = "Organize/sort imports"
expect(desc == "Organize/sort imports")
```

</details>

### CodeActionKind is_quick_fix

#### returns true for QuickFix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case QuickFix: true
val is_fix = true
expect(is_fix)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_fix = false
expect(not is_fix)
```

</details>

### CodeActionKind is_refactor

#### returns true for Refactor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Refactor: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns true for RefactorExtract

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorExtract: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns true for RefactorInline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorInline: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns true for RefactorRewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorRewrite: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_refactor = false
expect(not is_refactor)
```

</details>

### CodeActionKind is_source_action

#### returns true for Source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Source: true
val is_source = true
expect(is_source)
```

</details>

#### returns true for SourceOrganizeImports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case SourceOrganizeImports: true
val is_source = true
expect(is_source)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_source = false
expect(not is_source)
```

</details>

### CodeActionKind is_extract

#### returns true for RefactorExtract

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorExtract: true
val is_extract = true
expect(is_extract)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_extract = false
expect(not is_extract)
```

</details>

### CodeActionKind is_inline

#### returns true for RefactorInline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case RefactorInline: true
val is_inline = true
expect(is_inline)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_inline = false
expect(not is_inline)
```

</details>

### CodeActionKind summary

#### categorizes as fix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.is_quick_fix() (true)
val category = "fix"
expect(category == "fix")
```

</details>

#### categorizes as refactor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: elif self.is_refactor() (true)
val category = "refactor"
expect(category == "refactor")
```

</details>

#### categorizes as source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: else (default case)
val category = "source"
expect(category == "source")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/code_action_kind_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CodeActionKind to_string
- CodeActionKind description
- CodeActionKind is_quick_fix
- CodeActionKind is_refactor
- CodeActionKind is_source_action
- CodeActionKind is_extract
- CodeActionKind is_inline
- CodeActionKind summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
