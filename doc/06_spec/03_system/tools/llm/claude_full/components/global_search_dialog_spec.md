# Claude Full GlobalSearchDialog Component

> Checks global search query state, scoring, grouped rows, keyboard navigation, and summaries.

<!-- sdn-diagram:id=global_search_dialog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=global_search_dialog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

global_search_dialog_spec -> std
global_search_dialog_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=global_search_dialog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

## Scenarios

### opens closes queries and normalizes selection

- Create a closed dialog and open it.
- Expected: closed render is explicit.
- Expected: opening preserves a normalized selected index.
- Expected: query changes reset selection and close hides the dialog.

### scores and filters rows

- Search title, subtitle, path, and keywords.
- Expected: keyboard search returns the shortcuts help row.
- Expected: title match outranks keyword match.
- Expected: file category filtering returns the matching file row.

### groups categories and renders selected rows

- Render grouped rows with selected marker.
- Expected: results are grouped under category labels.
- Expected: rendered output includes visible count and selected marker.

### handles keyboard navigation and summaries

- Move through result rows and close with Escape.
- Expected: ArrowDown, ArrowUp, Home, End, Enter, and Escape update state.
- Expected: loading and error summaries are explicit.

### renders empty loading error and source helpers

- Pin summaries and upstream helper names.
- Expected: empty, loading, and error output are deterministic.
- Expected: category labels and modeled source helpers are exported.

## Source

Executable spec: `test/03_system/tools/llm/claude_full/components/global_search_dialog_spec.spl`
