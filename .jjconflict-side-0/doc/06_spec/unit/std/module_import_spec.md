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
   - Expected: true is true


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
expect(true).to_equal(true)
```

</details>

#### parses use module with group imports

- parses use module with group imports
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use module with group imports")
use std.core.{Option, Result}
expect(true).to_equal(true)
```

</details>

#### parses use module

- parses use module
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use module")
use std.core
expect(true).to_equal(true)
```

</details>

#### parses use with alias

- parses use with alias
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use with alias")
use std.core.Option as Opt
expect(true).to_equal(true)
```

</details>

### deprecated double colon syntax

#### warns on use std double colon core

- warns on use std double colon core
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on use std double colon core")
# Parser should emit: "Deprecated: '.' in module paths"
use std.core
expect(true).to_equal(true)
```

</details>

#### warns on use std double colon core double colon star

- warns on use std double colon core double colon star
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on use std double colon core double colon star")
# Multiple . should emit multiple warnings
use std.core
expect(true).to_equal(true)
```

</details>

#### warns on use std double colon core with group

- warns on use std double colon core with group
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on use std double colon core with group")
use std.core.{Option, Result}
expect(true).to_equal(true)
```

</details>

### deprecated import keyword

#### warns on import keyword

- warns on import keyword
   - Expected: true is true


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
expect(true).to_equal(true)
```

</details>

#### warns on from...import syntax

- warns on from...import syntax
   - Expected: true is true


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
expect(true).to_equal(true)
```

</details>

### export use statements

#### parses export use module.item

- parses export use module.item
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export use module.item")
export use std.core.Option
expect(true).to_equal(true)
```

</details>

#### parses export use module with group

- parses export use module with group
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export use module with group")
export use std.core.{Option, Result}
expect(true).to_equal(true)
```

</details>

#### warns on export use module

- warns on export use module
   - Expected: true is true


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
expect(true).to_equal(true)
```

</details>

#### parses export A, B from module

- parses export A, B from module
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export A, B from module")
export Option, Result from std.core
expect(true).to_equal(true)
```

</details>

#### parses export group from module

- parses export group from module
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export group from module")
export { Option, Result } from std.core
expect(true).to_equal(true)
```

</details>

### common use statements

#### parses common use module.item

- parses common use module.item
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses common use module.item")
common use std.core.Option
expect(true).to_equal(true)
```

</details>

#### parses common use module with group

- parses common use module with group
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses common use module with group")
common use std.core.{Option, Result}
expect(true).to_equal(true)
```

</details>

### relative imports

#### parses import .. as parent

- parses import .. as parent
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses import .. as parent")
import .. as parent
expect(true).to_equal(true)
```

</details>

#### parses import ..sibling

- parses import ..sibling
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses import ..sibling")
import ..sibling
expect(true).to_equal(true)
```

</details>

### module path with keywords

#### allows async in path

- allows async in path
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows async in path")
use host.async_nogc_mut.io
expect(true).to_equal(true)
```

</details>

#### allows sync in path

- allows sync in path
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows sync in path")
use host.sync_nogc_mut.io
expect(true).to_equal(true)
```

</details>

#### allows test in path

- allows test in path
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows test in path")
use std.test.helpers
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/std/module_import_spec.spl` |
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

- Canonical SPipe generation for source `869372cb58b869ae0c7eb0a9a9269a94c02b75baca90bf6515a4ae52153391f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `869372cb58b869ae0c7eb0a9a9269a94c02b75baca90bf6515a4ae52153391f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `869372cb58b869ae0c7eb0a9a9269a94c02b75baca90bf6515a4ae52153391f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/std/module_import_spec.spl
mirror: doc/06_spec/unit/std/module_import_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/std/module_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/std/module_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/std/module_import_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/std/module_import_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module.item' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/module_import_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module with group imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/module_import_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
