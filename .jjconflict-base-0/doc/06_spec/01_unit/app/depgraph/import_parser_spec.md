# Import Parser Specification

> Tests that the import parser correctly identifies import statements from source code strings.

<!-- sdn-diagram:id=import_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=import_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

import_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=import_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import Parser Specification

Tests that the import parser correctly identifies import statements from source code strings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/depgraph/import_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the import parser correctly identifies import statements
from source code strings.

## Scenarios

### Import Parser

#### parses source with no imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main(): 0\n"
val result = parse_source("test.spl", source)
expect(result.imports.len()).to_equal(0)
```

</details>

#### parses source with one import

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "import foo.bar\nfn main(): 0\n"
val result = parse_source("test.spl", source)
expect(result.imports.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
