# Browser Session Module Dependency Bounds Spec

> Inline, external, and cached ES modules share `extract_module_dependency_urls` before recursive module loading. Pathological module source must not create an unbounded dependency list or pending network request fan-out.

<!-- sdn-diagram:id=browser_session_module_dependency_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_module_dependency_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_module_dependency_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_module_dependency_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Module Dependency Bounds Spec

Inline, external, and cached ES modules share `extract_module_dependency_urls` before recursive module loading. Pathological module source must not create an unbounded dependency list or pending network request fan-out.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_module_dependency_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Inline, external, and cached ES modules share `extract_module_dependency_urls`
before recursive module loading. Pathological module source must not create an
unbounded dependency list or pending network request fan-out.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct dependency-list assertions.

## Scenarios

### BrowserSessionModuleDependencyBounds

#### caps unique module dependency extraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = browser_session_debug_max_module_dependencies()
var source = ""
var i = 0
while i < cap + 8:
    source = source + "import dep{i} from './dep{i}.js';\n"
    i = i + 1

val deps = extract_module_dependency_urls("https://example.com/app/main.js", source)
expect(deps.len()).to_equal(cap)
expect(deps[0]).to_equal("https://example.com/app/./dep0.js")
expect(deps[cap - 1]).to_equal("https://example.com/app/./dep63.js")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
