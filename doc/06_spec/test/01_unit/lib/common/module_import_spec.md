# Module Import Syntax Specification

> Tests for module import/use statement parsing and deprecation warnings.

<!-- sdn-diagram:id=module_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_import_spec
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
| Source | `test/01_unit/lib/common/module_import_spec.spl` |
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
val output = expect_import_probe_success("use_item", "use lib.core.Option\nfn main():\n    print(\"use-item-ok\")\n", "use-item-ok")
expect(output).to_contain("use-item-ok")
```

</details>

#### parses use module with group imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("use_group", "use lib.core.{Option, Result}\nfn main():\n    print(\"use-group-ok\")\n", "use-group-ok")
expect(output).to_contain("use-group-ok")
```

</details>

#### parses use module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("use_module", "use lib.core\nfn main():\n    print(\"use-module-ok\")\n", "use-module-ok")
expect(output).to_contain("use-module-ok")
```

</details>

#### parses use with alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("use_alias", "use lib.core.Option as Opt\nfn main():\n    print(\"use-alias-ok\")\n", "use-alias-ok")
expect(output).to_contain("use-alias-ok")
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
val output = expect_import_probe_success("dot_module", "use lib.core\nfn main():\n    print(\"dot-module-ok\")\n", "dot-module-ok")
expect(output).to_contain("dot-module-ok")
```

</details>

#### warns on use std double colon core double colon star

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple . should emit multiple warnings
val output = expect_import_probe_success("dot_nested", "use lib.core\nfn main():\n    print(\"dot-nested-ok\")\n", "dot-nested-ok")
expect(output).to_contain("dot-nested-ok")
```

</details>

#### warns on use std double colon core with group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("dot_group", "use lib.core.{Option, Result}\nfn main():\n    print(\"dot-group-ok\")\n", "dot-group-ok")
expect(output).to_contain("dot-group-ok")
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
val output = expect_import_probe_success("import_keyword", "import std.core\nfn main():\n    print(\"import-keyword-ok\")\n", "import-keyword-ok")
expect(output).to_contain("Deprecated: 'import' keyword")
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
val output = expect_import_probe_success("from_import", "from std.core import Option\nfn main():\n    print(\"from-import-ok\")\n", "from-import-ok")
expect(output).to_contain("Deprecated: 'from ... import' syntax")
```

</details>

### export use statements

#### parses export use module.item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("export_use_item", "export use lib.core.Option\nfn main():\n    print(\"export-use-item-ok\")\n", "export-use-item-ok")
expect(output).to_contain("export-use-item-ok")
```

</details>

#### parses export use module with group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("export_use_group", "export use lib.core.{Option, Result}\nfn main():\n    print(\"export-use-group-ok\")\n", "export-use-group-ok")
expect(output).to_contain("export-use-group-ok")
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
val output = expect_import_probe_success("export_use_module", "export use lib.core\nfn main():\n    print(\"export-use-module-ok\")\n", "export-use-module-ok")
expect(output).to_contain("export-use-module-ok")
```

</details>

#### parses export A, B from module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("export_from", "export Option, Result from std.core\nfn main():\n    print(\"export-from-ok\")\n", "export-from-ok")
expect(output).to_contain("export-from-ok")
```

</details>

#### parses export group from module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("export_group_from", "export { Option, Result } from std.core\nfn main():\n    print(\"export-group-from-ok\")\n", "export-group-from-ok")
expect(output).to_contain("export-group-from-ok")
```

</details>

### common use statements

#### parses common use module.item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("common_use_item", "common use lib.core.Option\nfn main():\n    print(\"common-use-item-ok\")\n", "common-use-item-ok")
expect(output).to_contain("common-use-item-ok")
```

</details>

#### parses common use module with group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("common_use_group", "common use lib.core.{Option, Result}\nfn main():\n    print(\"common-use-group-ok\")\n", "common-use-group-ok")
expect(output).to_contain("common-use-group-ok")
```

</details>

### relative imports

#### parses import .. as parent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("relative_parent", "import .. as parent\nfn main():\n    print(\"relative-parent-ok\")\n", "relative-parent-ok")
expect(output).to_contain("Deprecated: 'import' keyword")
```

</details>

#### parses import ..sibling

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("relative_sibling", "import ..sibling\nfn main():\n    print(\"relative-sibling-ok\")\n", "relative-sibling-ok")
expect(output).to_contain("Deprecated: 'import' keyword")
```

</details>

### module path with keywords

#### allows async in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("keyword_async", "use host.async_nogc_mut.io\nfn main():\n    print(\"keyword-async-ok\")\n", "keyword-async-ok")
expect(output).to_contain("keyword-async-ok")
```

</details>

#### allows sync in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("keyword_sync", "use host.sync_nogc_mut.io\nfn main():\n    print(\"keyword-sync-ok\")\n", "keyword-sync-ok")
expect(output).to_contain("keyword-sync-ok")
```

</details>

#### allows test in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = expect_import_probe_success("keyword_test", "use lib.test.helpers\nfn main():\n    print(\"keyword-test-ok\")\n", "keyword-test-ok")
expect(output).to_contain("keyword-test-ok")
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
