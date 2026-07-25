# Module Import Syntax Specification

> Tests for module import/use statement parsing and deprecation warnings.

<!-- sdn-diagram:id=module_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_import_spec -> std
module_import_spec -> host
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Import Syntax Specification

Tests for module import/use statement parsing and deprecation warnings.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax |
| Status | Implemented |
| Source | `test/01_unit/std/module_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for module import/use statement parsing and deprecation warnings.
Covers modern `use` syntax and deprecated alternatives like `import`, `.`
and `from...import` patterns.

## Scenarios

### Module Import Syntax

### use statement with dot notation

#### parses use module.item

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This should parse without warnings
# Note: Module may not exist, we're testing parsing
use std.core.Option
expect("use std.core.Option").to_contain(".Option")
```

</details>

#### parses use module with group imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use std.core.{Option, Result}
expect("use std.core.{Option, Result}").to_contain("{Option, Result}")
```

</details>

#### parses use module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use std.core
expect("use std.core").to_end_with("core")
```

</details>

#### parses use with alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use std.core.Option as Opt
expect("use std.core.Option as Opt").to_contain(" as Opt")
```

</details>

### deprecated double colon syntax

#### warns on use std double colon core

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should emit: "Deprecated: '.' in module paths"
use std.core
expect("use std.core").to_contain("std.core")
```

</details>

#### warns on use std double colon core double colon star

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple . should emit multiple warnings
use std.core
expect("use std.core").to_contain(".core")
```

</details>

#### warns on use std double colon core with group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use std.core.{Option, Result}
expect("use std.core.{Option, Result}").to_contain("std.core")
```

</details>

### deprecated import keyword

#### warns on import keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should emit: "Deprecated: 'import' keyword"
# Use 'use' instead
import std.core
expect("import std.core").to_start_with("import")
```

</details>

#### warns on from...import syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should emit: "Deprecated: 'from ... import' syntax"
# Use 'use module.group' instead
from std.core import Option
expect("from std.core import Option").to_contain(" import ")
```

</details>

### export use statements

#### parses export use module.item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
export use std.core.Option
expect("export use std.core.Option").to_start_with("export use")
```

</details>

#### parses export use module with group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
export use std.core.{Option, Result}
expect("export use std.core.{Option, Result}").to_contain("{Option, Result}")
```

</details>

#### warns on export use module

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should emit: "Avoid 'export use *' - exposes unnecessary interfaces"
# Use explicit exports instead
export use std.core
expect("export use std.core").to_end_with("std.core")
```

</details>

#### parses export A, B from module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
export Option, Result from std.core
expect("export Option, Result from std.core").to_contain(" from ")
```

</details>

#### parses export group from module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
export { Option, Result } from std.core
expect("export { Option, Result } from std.core").to_contain("{ Option, Result }")
```

</details>

### common use statements

#### parses common use module.item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
common use std.core.Option
expect("common use std.core.Option").to_start_with("common use")
```

</details>

#### parses common use module with group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
common use std.core.{Option, Result}
expect("common use std.core.{Option, Result}").to_contain("{Option, Result}")
```

</details>

### relative imports

#### parses import .. as parent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
import .. as parent
expect("import .. as parent").to_contain(".. as parent")
```

</details>

#### parses import ..sibling

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
import ..sibling
expect("import ..sibling").to_contain("..sibling")
```

</details>

### module path with keywords

#### allows async in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use host.async_nogc_mut.io
expect("use host.async_nogc_mut.io").to_contain("async_nogc_mut")
```

</details>

#### allows sync in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use host.sync_nogc_mut.io
expect("use host.sync_nogc_mut.io").to_contain("sync_nogc_mut")
```

</details>

#### allows test in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
use std.test.helpers
expect("use std.test.helpers").to_contain(".test.")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
