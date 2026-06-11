# Extension Roots Specification

> <details>

<!-- sdn-diagram:id=extension_roots_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=extension_roots_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

extension_roots_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=extension_roots_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extension Roots Specification

## Scenarios

### editor extension root policy

#### keeps VS Code-like workspace roots in shared lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val roots = editor_extension_workspace_roots()
expect(roots.len()).to_equal(2)
expect(roots[0]).to_equal(".simple/editor/extensions")
expect(roots[1]).to_equal(".vscode/simple-editor/extensions")
```

</details>

#### merges configured, user, and system roots without runtime env access

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val roots = editor_extension_roots_from_inputs("/opt/a:/opt/b", "/home/dev")
expect(roots.len()).to_equal(8)
expect(roots[0]).to_equal(".simple/editor/extensions")
expect(roots[1]).to_equal(".vscode/simple-editor/extensions")
expect(roots[2]).to_equal("/opt/a")
expect(roots[3]).to_equal("/opt/b")
expect(roots[4]).to_equal("/home/dev/.simple/editor/extensions")
expect(roots[5]).to_equal("/home/dev/.simple/extensions")
expect(roots[6]).to_equal("/usr/local/share/simple/editor/extensions")
expect(roots[7]).to_equal("/usr/share/simple/editor/extensions")
```

</details>

#### omits user roots when home is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val roots = editor_extension_roots_from_inputs("", "")
expect(roots.len()).to_equal(4)
expect(roots[0]).to_equal(".simple/editor/extensions")
expect(roots[1]).to_equal(".vscode/simple-editor/extensions")
expect(roots[2]).to_equal("/usr/local/share/simple/editor/extensions")
expect(roots[3]).to_equal("/usr/share/simple/editor/extensions")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/extension_roots_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor extension root policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
