# Browser Session Modules Specification

> <details>

<!-- sdn-diagram:id=browser_session_modules_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_modules_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_modules_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_modules_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Modules Specification

## Scenarios

### BrowserSession module transforms

#### extracts inline and external script blocks with stable attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><script src='/app.js' type='module' defer></script><script>document.title = 'Runtime Ready';</script></body></html>"

val blocks = extract_script_blocks(html)

expect(blocks.len()).to_equal(2)
expect(blocks[0].kind).to_equal("external")
expect(blocks[0].src).to_equal("/app.js")
expect(blocks[0].script_type).to_equal("module")
expect(blocks[0].is_defer).to_equal(true)
expect(blocks[1].kind).to_equal("inline")
expect(blocks[1].content).to_equal("document.title = 'Runtime Ready';")
```

</details>

#### extracts dependency URLs from imports and re-exports once

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "import def from './dep.js';\nexport \{ named \} from './dep.js';\nexport * from '../shared.js';"

val deps = extract_module_dependency_urls("https://example.com/app/main.js", source)

expect(deps.len()).to_equal(2)
expect(deps[0]).to_equal("https://example.com/app/./dep.js")
expect(deps[1]).to_equal("https://example.com/app/../shared.js")
```

</details>

#### transforms import and export statements without changing module names

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = [Pair(first: "https://example.com/app/../shared.js", second: "export const shared = 1; export const hidden = 2;")]

val transformed = transform_module_source(
    "https://example.com/app/main.js",
    "import def, \{ named as alias \} from './dep.js';\nexport const local = alias;\nexport * from '../shared.js';",
    cache
)

expect(transformed).to_contain("var __simple_module_https___example_com_app_main_js = {};")
expect(transformed).to_contain("var alias = __simple_module_https___example_com_app___dep_js.named;")
expect(transformed).to_contain("var local = alias;")
expect(transformed).to_contain("__simple_module.local = local;")
expect(transformed).to_contain("if (__simple_module.shared == undefined)")
```

</details>

#### normalizes module symbols and finds matching braces across quoted text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suffix = module_symbol_suffix("https://example.com/app/main.js")
val close = find_matching_brace("function demo() { return '{ignored}'; } tail", 16)

expect(suffix).to_equal("https___example_com_app_main_js")
expect(close).to_equal(38)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_modules_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession module transforms

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
