# Claude Full Grove Component

> Checks modern SSpec parity for Grove tree state, rendering, and navigation helpers.

<!-- sdn-diagram:id=grove_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=grove_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

grove_spec -> std
grove_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=grove_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Grove Component

Checks modern SSpec parity for Grove tree state, rendering, and navigation helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/grove_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for Grove tree state, rendering, and navigation helpers.

## Scenarios

### Claude full Grove component

#### should render sample grove rows and breadcrumbs

- Create sample Grove model


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create sample Grove model")
val roots = sampleGroveNodes()
val grove = createGrove(roots)
expect(grove.render()).to_contain("Grove")
expect(grove.activeBreadcrumbs().len()).to_be_greater_than(0)
```

</details>

#### should navigate and filter grove nodes

- Navigate visible rows
   - Expected: selectNextGroveNode(roots, state).activeId equals `workspace`
   - Expected: handleGroveKey(roots, state, "end").activeId equals `workspace`
- Filter by query


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Navigate visible rows")
val roots = sampleGroveNodes()
val state = GroveState.empty()
expect(selectNextGroveNode(roots, state).activeId).to_equal("workspace")
expect(handleGroveKey(roots, state, "end").activeId).to_equal("workspace")

step("Filter by query")
val filtered = GroveState.empty().withQuery("Grove")
expect(renderGrove(roots, filtered)).to_contain("Grove.spl")
```

</details>

#### should check modeled TypeScript source floor

- Read Grove source helper
   - Expected: groveSourceLinesModeled() equals `462`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read Grove source helper")
expect(groveSourceLinesModeled()).to_equal(462)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
