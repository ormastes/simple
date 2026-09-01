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
val output = expect_import_probe_success("use_item", "use lib.core.Option\nfn main():\n    print(\"use-item-ok\")\n", "use-item-ok")
expect(output).to_contain("use-item-ok")
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
val output = expect_import_probe_success("use_group", "use lib.core.{Option, Result}\nfn main():\n    print(\"use-group-ok\")\n", "use-group-ok")
expect(output).to_contain("use-group-ok")
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
val output = expect_import_probe_success("use_module", "use lib.core\nfn main():\n    print(\"use-module-ok\")\n", "use-module-ok")
expect(output).to_contain("use-module-ok")
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
val output = expect_import_probe_success("use_alias", "use lib.core.Option as Opt\nfn main():\n    print(\"use-alias-ok\")\n", "use-alias-ok")
expect(output).to_contain("use-alias-ok")
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
val output = expect_import_probe_success("dot_module", "use lib.core\nfn main():\n    print(\"dot-module-ok\")\n", "dot-module-ok")
expect(output).to_contain("dot-module-ok")
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
val output = expect_import_probe_success("dot_nested", "use lib.core\nfn main():\n    print(\"dot-nested-ok\")\n", "dot-nested-ok")
expect(output).to_contain("dot-nested-ok")
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
val output = expect_import_probe_success("dot_group", "use lib.core.{Option, Result}\nfn main():\n    print(\"dot-group-ok\")\n", "dot-group-ok")
expect(output).to_contain("dot-group-ok")
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
val output = expect_import_probe_success("import_keyword", "import std.core\nfn main():\n    print(\"import-keyword-ok\")\n", "import-keyword-ok")
expect(output).to_contain("Deprecated: 'import' keyword")
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
val output = expect_import_probe_success("from_import", "from std.core import Option\nfn main():\n    print(\"from-import-ok\")\n", "from-import-ok")
expect(output).to_contain("Deprecated: 'from ... import' syntax")
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
val output = expect_import_probe_success("export_use_item", "export use lib.core.Option\nfn main():\n    print(\"export-use-item-ok\")\n", "export-use-item-ok")
expect(output).to_contain("export-use-item-ok")
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
val output = expect_import_probe_success("export_use_group", "export use lib.core.{Option, Result}\nfn main():\n    print(\"export-use-group-ok\")\n", "export-use-group-ok")
expect(output).to_contain("export-use-group-ok")
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
val output = expect_import_probe_success("export_use_module", "export use lib.core\nfn main():\n    print(\"export-use-module-ok\")\n", "export-use-module-ok")
expect(output).to_contain("export-use-module-ok")
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
val output = expect_import_probe_success("export_from", "export exact_ratio, exact_ratio_mul from std.common.units.model.world_units\nfn main():\n    print(\"export-from-ok\")\n", "export-from-ok")
expect(output).to_contain("export-from-ok")
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
val output = expect_import_probe_success("export_group_from", "export { exact_ratio, exact_ratio_mul } from std.common.units.model.world_units\nfn main():\n    print(\"export-group-from-ok\")\n", "export-group-from-ok")
expect(output).to_contain("export-group-from-ok")
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
val output = expect_import_probe_success("common_use_item", "common use lib.core.Option\nfn main():\n    print(\"common-use-item-ok\")\n", "common-use-item-ok")
expect(output).to_contain("common-use-item-ok")
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
val output = expect_import_probe_success("common_use_group", "common use lib.core.{Option, Result}\nfn main():\n    print(\"common-use-group-ok\")\n", "common-use-group-ok")
expect(output).to_contain("common-use-group-ok")
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
val output = expect_import_probe_success("relative_parent", "import .. as parent\nfn main():\n    print(\"relative-parent-ok\")\n", "relative-parent-ok")
expect(output).to_contain("Deprecated: 'import' keyword")
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
val output = expect_import_probe_success("relative_sibling", "import ..sibling\nfn main():\n    print(\"relative-sibling-ok\")\n", "relative-sibling-ok")
expect(output).to_contain("Deprecated: 'import' keyword")
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
val output = expect_import_probe_success("keyword_async", "use std.nogc_async_mut.async\nfn main():\n    print(\"keyword-async-ok\")\n", "keyword-async-ok")
expect(output).to_contain("keyword-async-ok")
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
val output = expect_import_probe_success("keyword_sync", "use std.nogc_async_mut.async.sync\nfn main():\n    print(\"keyword-sync-ok\")\n", "keyword-sync-ok")
expect(output).to_contain("keyword-sync-ok")
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
val output = expect_import_probe_success("keyword_test", "use std.nogc_sync_mut.test\nfn main():\n    print(\"keyword-test-ok\")\n", "keyword-test-ok")
expect(output).to_contain("keyword-test-ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/module_import_spec.spl` |
| Updated | 2026-08-27 |
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

- Canonical SPipe generation for source `40d48f7327cd2809796b0f346089f58fd63abec522389b18a221a343cffb6d9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40d48f7327cd2809796b0f346089f58fd63abec522389b18a221a343cffb6d9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40d48f7327cd2809796b0f346089f58fd63abec522389b18a221a343cffb6d9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/common/module_import_spec.spl
mirror: doc/06_spec/unit/lib/common/module_import_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/module_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/module_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/module_import_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/lib/common/module_import_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module.item' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/module_import_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module with group imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/module_import_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
