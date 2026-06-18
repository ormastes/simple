# Browser Session Script Block Bounds Spec

> Classic JavaScript, ES modules, WASM script tags, and `text/simple` script tags all start from `extract_script_blocks`. Pathological HTML must not create an unbounded script block queue before the later per-runtime guards run.

<!-- sdn-diagram:id=browser_session_script_block_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_script_block_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_script_block_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_script_block_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Script Block Bounds Spec

Classic JavaScript, ES modules, WASM script tags, and `text/simple` script tags all start from `extract_script_blocks`. Pathological HTML must not create an unbounded script block queue before the later per-runtime guards run.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_script_block_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Classic JavaScript, ES modules, WASM script tags, and `text/simple` script tags
all start from `extract_script_blocks`. Pathological HTML must not create an
unbounded script block queue before the later per-runtime guards run.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct script block assertions.

## Scenarios

### BrowserSessionScriptBlockBounds

#### caps extracted script blocks while preserving source order

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = browser_session_debug_max_script_blocks()
var html = "<html><body>"
var i = 0
while i < cap + 8:
    html = html + "<script>var s{i} = {i};</script>"
    i = i + 1
html = html + "</body></html>"

val blocks = extract_script_blocks(html)
expect(blocks.len()).to_equal(cap)
expect(blocks[0].content).to_equal("var s0 = 0;")
expect(blocks[cap - 1].content).to_equal("var s127 = 127;")
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
