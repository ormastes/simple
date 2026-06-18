# Simple Web HTML Layout Count-Pass Specification

> This focused unit spec guards the HTML layout parser count pass used for arena preallocation. It covers decoded entity-only whitespace so the count pass stays aligned with the parser's actual node materialization behavior.

<!-- sdn-diagram:id=simple_web_html_layout_count_pass_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_html_layout_count_pass_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_html_layout_count_pass_spec -> std
simple_web_html_layout_count_pass_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_html_layout_count_pass_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web HTML Layout Count-Pass Specification

This focused unit spec guards the HTML layout parser count pass used for arena preallocation. It covers decoded entity-only whitespace so the count pass stays aligned with the parser's actual node materialization behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md |
| Design | doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused unit spec guards the HTML layout parser count pass used for arena
preallocation. It covers decoded entity-only whitespace so the count pass stays
aligned with the parser's actual node materialization behavior.

**Plan:** doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md

**Requirements:** N/A

**Design:** doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md

**Research:** N/A

## Syntax

The spec uses `std.spec` scenarios and direct value matchers. It compares the
renderer's allocated parser arena length against the count of materialized
nodes for an `&nbsp;` tail-whitespace document.

## Scenarios

### SimpleWebHtmlLayoutCountPass

#### allocates the same count the parser materializes for decoded entity-only tail whitespace

- Parse a document with entity-only whitespace after the document element
- Assert arena preallocation matches materialized parser nodes
   - Expected: allocated_count equals `materialized_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a document with entity-only whitespace after the document element")
val html = "<html><body><div id='box'></div></body></html>&nbsp;"
val allocated_count = simple_web_layout_debug_node_count(html)
val materialized_count = simple_web_layout_debug_materialized_node_count(html)

step("Assert arena preallocation matches materialized parser nodes")
expect(allocated_count).to_equal(materialized_count)
expect(materialized_count).to_be_greater_than(4)
```

</details>

#### caps parser arena allocation for oversized element streams

- Parse more element nodes than the layout renderer admits
- Assert allocation and materialization stop at the explicit node cap
   - Expected: allocated_count equals `simple_web_layout_debug_max_node_count()`
   - Expected: materialized_count equals `simple_web_layout_debug_max_node_count()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse more element nodes than the layout renderer admits")
val html = "<main>" + str_repeat("<div></div>", simple_web_layout_debug_max_node_count() + 32) + "</main>"
val allocated_count = simple_web_layout_debug_node_count(html)
val materialized_count = simple_web_layout_debug_materialized_node_count(html)

step("Assert allocation and materialization stop at the explicit node cap")
expect(allocated_count).to_equal(simple_web_layout_debug_max_node_count())
expect(materialized_count).to_equal(simple_web_layout_debug_max_node_count())
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


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md](doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md)
- **Design:** [doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md](doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md)


</details>
