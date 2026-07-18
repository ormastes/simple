# Cmm Dialog Label Ref Specification

> <details>

<!-- sdn-diagram:id=cmm_dialog_label_ref_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cmm_dialog_label_ref_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cmm_dialog_label_ref_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cmm_dialog_label_ref_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cmm Dialog Label Ref Specification

## Scenarios

### CMM Dialog Label Reference Checking

#### valid references

#### produces no warnings for valid label refs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = dlr_analyze_refs(cmm_valid_refs())
expect(diags.len()).to_equal(0)
```

</details>

#### accepts DIALOG.Set with declared label

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val labels = dlr_collect_labels(cmm_valid_refs())
val diags = dlr_check_refs("DIALOG.Set mycheck", labels)
expect(diags.len()).to_equal(0)
```

</details>

#### accepts DIALOG.EXECUTE with declared label

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val labels = dlr_collect_labels(cmm_valid_refs())
val diags = dlr_check_refs("DIALOG.EXECUTE ok_btn", labels)
expect(diags.len()).to_equal(0)
```

</details>

#### invalid references

#### warns on undeclared label in DIALOG.Set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = dlr_analyze_refs(cmm_invalid_ref())
expect(diags.len()).to_equal(1)
expect(diags[0].message).to_contain("nonexistent")
```

</details>

#### warns on undeclared label in EVAL DIALOG.BOOLEAN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = dlr_analyze_refs(cmm_eval_invalid())
expect(diags.len()).to_equal(1)
expect(diags[0].message).to_contain("missing_label")
```

</details>

#### macro references skipped

#### does not warn on macro reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = dlr_analyze_refs(cmm_macro_ref())
expect(diags.len()).to_equal(0)
```

</details>

#### no dialog blocks

#### produces no warnings when no DIALOG blocks exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = dlr_analyze_refs(cmm_no_dialog())
expect(diags.len()).to_equal(0)
```

</details>

#### multiple dialog blocks

#### collects labels from both blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val labels = dlr_collect_labels(cmm_multi_dialog())
expect(labels.len()).to_equal(2)
```

</details>

#### validates refs against labels from all blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = dlr_analyze_refs(cmm_multi_dialog())
expect(diags.len()).to_equal(0)
```

</details>

#### label collection

#### collects edit labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val labels = dlr_collect_labels("DIALOG\n(\n  myedit: EDIT \"\" \"\"\n)")
expect(labels.len()).to_equal(1)
```

</details>

#### collects checkbox labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val labels = dlr_collect_labels("DIALOG\n(\n  mycb: CHECKBOX \"C\" \"\"\n)")
expect(labels.len()).to_equal(1)
```

</details>

#### does not collect HEADER as label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val labels = dlr_collect_labels("DIALOG\n(\n  HEADER \"Title\"\n)")
expect(labels.len()).to_equal(0)
```

</details>

#### does not collect TEXT as label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val labels = dlr_collect_labels("DIALOG\n(\n  TEXT \"Info\"\n)")
expect(labels.len()).to_equal(0)
```

</details>

#### duplicate labels

#### detects duplicate labels in a dialog block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duplicates = dlr_collect_duplicate_labels(cmm_duplicate_labels())
expect(duplicates).to_contain("same")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cmm_lsp/cmm_dialog_label_ref_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CMM Dialog Label Reference Checking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
