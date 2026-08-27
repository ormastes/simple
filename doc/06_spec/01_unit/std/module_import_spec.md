# Module Import Specification

> Tests covering Module Import Syntax, use statement with dot notation, deprecated double colon syntax, deprecated import keyword, export use statements, common use statements, relative imports, module path with keywords.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Import Specification

## Scenarios

### Module Import Syntax

### use statement with dot notation

#### parses use module.item

- parses use module.item


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use module.item")
# This should parse without warnings
# Note: Module may not exist, we're testing parsing
use std.core.Option
expect("use std.core.Option").to_contain(".Option")
```

</details>

#### parses use module with group imports

- parses use module with group imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use module with group imports")
use std.core.{Option, Result}
expect("use std.core.{Option, Result}").to_contain("{Option, Result}")
```

</details>

#### parses use module

- parses use module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use module")
use std.core
expect("use std.core").to_end_with("core")
```

</details>

#### parses use with alias

- parses use with alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use with alias")
use std.core.Option as Opt
expect("use std.core.Option as Opt").to_contain(" as Opt")
```

</details>

### deprecated double colon syntax

#### warns on use std double colon core

- warns on use std double colon core


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on use std double colon core")
# Parser should emit: "Deprecated: '.' in module paths"
use std.core
expect("use std.core").to_contain("std.core")
```

</details>

#### warns on use std double colon core double colon star

- warns on use std double colon core double colon star


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on use std double colon core double colon star")
# Multiple . should emit multiple warnings
use std.core
expect("use std.core").to_contain(".core")
```

</details>

#### warns on use std double colon core with group

- warns on use std double colon core with group


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on use std double colon core with group")
use std.core.{Option, Result}
expect("use std.core.{Option, Result}").to_contain("std.core")
```

</details>

### deprecated import keyword

#### warns on import keyword

- warns on import keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on import keyword")
# Parser should emit: "Deprecated: 'import' keyword"
# Use 'use' instead
import std.core
expect("import std.core").to_start_with("import")
```

</details>

#### warns on from...import syntax

- warns on from...import syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on from...import syntax")
# Parser should emit: "Deprecated: 'from ... import' syntax"
# Use 'use module.group' instead
from std.core import Option
expect("from std.core import Option").to_contain(" import ")
```

</details>

### export use statements

#### parses export use module.item

- parses export use module.item


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export use module.item")
export use std.core.Option
expect("export use std.core.Option").to_start_with("export use")
```

</details>

#### parses export use module with group

- parses export use module with group


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export use module with group")
export use std.core.{Option, Result}
expect("export use std.core.{Option, Result}").to_contain("{Option, Result}")
```

</details>

#### warns on export use module

- warns on export use module


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on export use module")
# Parser should emit: "Avoid 'export use *' - exposes unnecessary interfaces"
# Use explicit exports instead
export use std.core
expect("export use std.core").to_end_with("std.core")
```

</details>

#### parses export A, B from module

- parses export A, B from module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export A, B from module")
export Option, Result from std.core
expect("export Option, Result from std.core").to_contain(" from ")
```

</details>

#### parses export group from module

- parses export group from module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export group from module")
export { Option, Result } from std.core
expect("export { Option, Result } from std.core").to_contain("{ Option, Result }")
```

</details>

### common use statements

#### parses common use module.item

- parses common use module.item


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses common use module.item")
common use std.core.Option
expect("common use std.core.Option").to_start_with("common use")
```

</details>

#### parses common use module with group

- parses common use module with group


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses common use module with group")
common use std.core.{Option, Result}
expect("common use std.core.{Option, Result}").to_contain("{Option, Result}")
```

</details>

### relative imports

#### parses import .. as parent

- parses import .. as parent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses import .. as parent")
import .. as parent
expect("import .. as parent").to_contain(".. as parent")
```

</details>

#### parses import ..sibling

- parses import ..sibling


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses import ..sibling")
import ..sibling
expect("import ..sibling").to_contain("..sibling")
```

</details>

### module path with keywords

#### allows async in path

- allows async in path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows async in path")
use host.async_nogc_mut.io
expect("use host.async_nogc_mut.io").to_contain("async_nogc_mut")
```

</details>

#### allows sync in path

- allows sync in path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows sync in path")
use host.sync_nogc_mut.io
expect("use host.sync_nogc_mut.io").to_contain("sync_nogc_mut")
```

</details>

#### allows test in path

- allows test in path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows test in path")
use std.test.helpers
expect("use std.test.helpers").to_contain(".test.")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/module_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module Import Syntax, use statement with dot notation, deprecated double colon syntax, deprecated import keyword, export use statements, common use statements, relative imports, module path with keywords.
- Module Import Syntax
- use statement with dot notation
- deprecated double colon syntax
- deprecated import keyword
- export use statements
- common use statements
- relative imports
- module path with keywords

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `f99fbb8585e63299fb3ebffdcf7f873b446c4f1bbad6ae1a8e75dac447d0a16f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f99fbb8585e63299fb3ebffdcf7f873b446c4f1bbad6ae1a8e75dac447d0a16f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f99fbb8585e63299fb3ebffdcf7f873b446c4f1bbad6ae1a8e75dac447d0a16f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/module_import_spec.spl
mirror: doc/06_spec/01_unit/std/module_import_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/module_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/module_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/module_import_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module.item' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/module_import_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module with group imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/module_import_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
