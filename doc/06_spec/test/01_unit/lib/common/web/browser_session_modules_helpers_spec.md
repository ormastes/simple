# Browser Session Modules Helpers Specification

> <details>

<!-- sdn-diagram:id=browser_session_modules_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_modules_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_modules_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_modules_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Modules Helpers Specification

## Scenarios

### BrowserSession module helpers

#### splits module statements across quoted semicolons and block exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "import def, { named as alias, other } from './dep.js';\nexport default function demo() { return 'a;b'; }\nexport const one = 1, two = call([1, 2]);"

val statements = split_module_statements(source)

expect(statements.len()).to_equal(3)
expect(statements[0]).to_equal("import def, { named as alias, other } from './dep.js';")
expect(statements[1]).to_equal("export default function demo() { return 'a;b'; }")
expect(statements[2]).to_equal("export const one = 1, two = call([1, 2]);")
```

</details>

#### splits import bindings and export declarators at top-level commas only

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = split_import_bindings("def, { named as alias, other }")
val declarators = split_export_binding_declarators("one = 1, two = call([1, 2]), three = ['a,b']")

expect(bindings.len()).to_equal(2)
expect(bindings[0].trim()).to_equal("def")
expect(bindings[1].trim()).to_equal("{ named as alias, other }")
expect(declarators.len()).to_equal(3)
expect(declarators[0].trim()).to_equal("one = 1")
expect(declarators[1].trim()).to_equal("two = call([1, 2])")
expect(declarators[2].trim()).to_equal("three = ['a,b']")
```

</details>

#### splits generic text using repeated delimiters without dropping trailing parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_text("alpha::beta::", "::")

expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("alpha")
expect(parts[1]).to_equal("beta")
expect(parts[2]).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_modules_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession module helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
