# Editor Gui Specification

> <details>

<!-- sdn-diagram:id=editor_gui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_gui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_gui_spec -> std
editor_gui_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_gui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 80 | 80 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Gui Specification

## Scenarios

### editor platform — detection

#### defines EditorPlatform enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("enum EditorPlatform:")).to_equal(true)
expect(src.contains("Desktop")).to_equal(true)
expect(src.contains("SimpleOS")).to_equal(true)
expect(src.contains("Web")).to_equal(true)
```

</details>

#### defines PlatformConfig with resource limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("struct PlatformConfig:")).to_equal(true)
expect(src.contains("max_open_files: i64")).to_equal(true)
expect(src.contains("max_undo_depth: i64")).to_equal(true)
expect(src.contains("file_watcher_enabled: bool")).to_equal(true)
```

</details>

#### has platform_default_config per platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("fn platform_default_config(platform: EditorPlatform) -> PlatformConfig")).to_equal(true)
```

</details>

### editor config — SDN settings

#### defines EditorConfig with theme, tab_size, etc

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("struct EditorConfig:")).to_equal(true)
expect(src.contains("theme: text")).to_equal(true)
expect(src.contains("tab_size: i64")).to_equal(true)
expect(src.contains("line_numbers: bool")).to_equal(true)
expect(src.contains("auto_save: bool")).to_equal(true)
expect(src.contains("hover_delay_ms: i64")).to_equal(true)
```

</details>

#### has editor_config_default with sensible defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_default() -> EditorConfig")).to_equal(true)
expect(editor_config_default().hover_delay_ms).to_equal(300)
expect(editor_config_get_by_key(editor_config_set_by_key(editor_config_default(), "hover_delay_ms", "125"), "hover_delay_ms")).to_equal("125")
```

</details>

#### has editor_config_load with layered merge

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_load(user_path: text, workspace_path: text) -> EditorConfig")).to_equal(true)
```

</details>

### editor TUI backend — formalized

#### defines TuiBackendConfig

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/tui_backend.spl")
expect(src.contains("struct TuiBackendConfig:")).to_equal(true)
expect(src.contains("color_mode: text")).to_equal(true)
expect(src.contains("line_numbers: bool")).to_equal(true)
```

</details>

#### has tui_backend_render_line and tui_backend_render_status

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/tui_backend.spl")
expect(src.contains("fn tui_backend_render_line")).to_equal(true)
expect(src.contains("fn tui_backend_render_status")).to_equal(true)
```

</details>

### editor GUI backend — Surface integration

#### defines GuiBackendConfig

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("struct GuiBackendConfig:")).to_equal(true)
expect(src.contains("window_title: text")).to_equal(true)
expect(src.contains("initial_width: i64")).to_equal(true)
```

</details>

#### has gui_render_markdown_block for HTML output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("fn gui_render_markdown_block(block: RenderBlock) -> GuiRenderBlock")).to_equal(true)
```

</details>

#### renders Obsidian callout blocks with GUI metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 9, kind: "callout", from_line: 0, to_line: 1, content: "> [!TIP]+ Useful\n> Use [[links]]", rendered_lines: ["> [!TIP]+ Useful", "> Use [[links]]"], status: "ok")
val rendered = gui_render_markdown_block(block)
expect(rendered.html.contains("class=\"md-callout md-callout-tip\"")).to_equal(true)
expect(rendered.html.contains("data-callout=\"tip\"")).to_equal(true)
expect(rendered.html.contains("data-folded=\"false\"")).to_equal(true)
expect(rendered.html.contains("data-source-from=\"0\"")).to_equal(true)
expect(rendered.html.contains("data-source-to=\"1\"")).to_equal(true)
expect(rendered.html.contains("class=\"md-callout-title-text\"")).to_equal(true)
expect(rendered.html.contains("<p data-line=\"1\">Use [[links]]</p>")).to_equal(true)
expect(rendered.html.contains("data-event=\"callout-fold-toggle\"")).to_equal(true)
expect(rendered.html.contains("TIP Useful")).to_equal(true)
expect(rendered.html.contains("Use [[links]]")).to_equal(true)
expect(rendered.html.contains("[!TIP]")).to_equal(false)

val folded_block = RenderBlock(id: 10, kind: "callout", from_line: 0, to_line: 1, content: "> [!TIP]- Useful\n> Hidden", rendered_lines: ["> [!TIP]- Useful", "> Hidden"], status: "ok")
val folded = gui_render_markdown_block(folded_block)
expect(folded.html.contains("data-folded=\"true\"")).to_equal(true)
expect(folded.html.contains("class=\"md-callout md-callout-tip folded\"")).to_equal(true)
expect(folded.html.contains("Hidden")).to_equal(false)
```

</details>

#### renders Obsidian embed blocks with GUI metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 10, kind: "embed", from_line: 0, to_line: 0, content: "![[Project Alpha|Alpha embed]]", rendered_lines: ["![[Project Alpha|Alpha embed]]"], status: "ok")
val rendered = gui_render_markdown_block(block)
expect(rendered.html.contains("class=\"md-embed md-embed-note\"")).to_equal(true)
expect(rendered.html.contains("data-embed-kind=\"note\"")).to_equal(true)
expect(rendered.html.contains("data-target=\"Project Alpha\"")).to_equal(true)
expect(rendered.html.contains("Alpha embed")).to_equal(true)
expect(rendered.html.contains("![[")).to_equal(false)
```

</details>

#### renders resolved Obsidian note embeds as GUI transclusions

1. md wiki document
   - Expected: rendered.html contains `md-transclusion`
   - Expected: rendered.html contains `data-target="Project Alpha"`
   - Expected: rendered.html contains `Project Alpha`
   - Expected: rendered.html contains `Body &lt;safe&gt;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 10, kind: "embed", from_line: 0, to_line: 0, content: "![[Project Alpha|Alpha embed]]", rendered_lines: ["![[Project Alpha|Alpha embed]]"], status: "ok")
val index = md_wiki_index_documents([
    md_wiki_document("/vault/Project Alpha.md", "# Project Alpha\nBody <safe>")
])
val rendered = gui_render_markdown_block_with_wiki(block, index)
expect(rendered.html.contains("md-transclusion")).to_equal(true)
expect(rendered.html.contains("data-target=\"Project Alpha\"")).to_equal(true)
expect(rendered.html.contains("Project Alpha")).to_equal(true)
expect(rendered.html.contains("Body &lt;safe&gt;")).to_equal(true)
```

</details>

#### renders nested resolved Obsidian note embeds as GUI transclusions

1. md wiki document
2. md wiki document
   - Expected: rendered.html contains `data-target="Project Alpha"`
   - Expected: rendered.html contains `data-target="Project Beta"`
   - Expected: rendered.html contains `Beta embed`
   - Expected: rendered.html contains `Nested body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 11, kind: "embed", from_line: 0, to_line: 0, content: "![[Project Alpha|Alpha embed]]", rendered_lines: ["![[Project Alpha|Alpha embed]]"], status: "ok")
val index = md_wiki_index_documents([
    md_wiki_document("/vault/Project Alpha.md", "# Project Alpha\n![[Project Beta|Beta embed]]"),
    md_wiki_document("/vault/Project Beta.md", "# Project Beta\nNested body")
])
val rendered = gui_render_markdown_block_with_wiki(block, index)
expect(rendered.html.contains("data-target=\"Project Alpha\"")).to_equal(true)
expect(rendered.html.contains("data-target=\"Project Beta\"")).to_equal(true)
expect(rendered.html.contains("Beta embed")).to_equal(true)
expect(rendered.html.contains("Nested body")).to_equal(true)
```

</details>

#### renders wiki property panels as editable GUI forms

1. WikiPanelRow
   - Expected: html contains `class="wiki-property-form"`
   - Expected: html contains `data-command="wiki-property-set"`
   - Expected: html contains `class="wiki-property-value"`
   - Expected: html contains `data-event="wiki-property-submit"`
   - Expected: html contains `data-payload="status|active"`
   - Expected: vault_html contains `data-event="wiki-vault-property-submit"`
   - Expected: vault_html contains `data-payload="" + vault_root + "|status|active"`
   - Expected: vault_html contains `data-event="wiki-vault-property-review"`
   - Expected: schema_html contains `<select class="wiki-property-value schema-aware"`
   - Expected: schema_html contains `data-required="required"`
   - Expected: schema_html contains `<option value="active" selected>active</option>`
   - Expected: schema_html contains `<option value="draft">draft</option>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_with_rows("Properties", [
    WikiPanelRow(icon: "property", label: "status", detail: "active", path: editor_gui_tmp_path("note.md"), line: 0)
])
val html = gui_render_wiki_property_form_html(panel)
expect(html.contains("class=\"wiki-property-form\"")).to_equal(true)
expect(html.contains("data-command=\"wiki-property-set\"")).to_equal(true)
expect(html.contains("class=\"wiki-property-value\"")).to_equal(true)
expect(html.contains("data-event=\"wiki-property-submit\"")).to_equal(true)
expect(html.contains("data-payload=\"status|active\"")).to_equal(true)
val vault_root = editor_gui_tmp_path("vault")
val vault_html = gui_render_wiki_property_form_html_with_root(panel, vault_root)
expect(vault_html.contains("data-event=\"wiki-vault-property-submit\"")).to_equal(true)
expect(vault_html.contains("data-payload=\"" + vault_root + "|status|active\"")).to_equal(true)
expect(vault_html.contains("data-event=\"wiki-vault-property-review\"")).to_equal(true)
val schema_html = gui_render_wiki_property_form_html_with_root_and_schema(panel, vault_root, "status|required|active,draft")
expect(schema_html.contains("<select class=\"wiki-property-value schema-aware\"")).to_equal(true)
expect(schema_html.contains("data-required=\"required\"")).to_equal(true)
expect(schema_html.contains("<option value=\"active\" selected>active</option>")).to_equal(true)
expect(schema_html.contains("<option value=\"draft\">draft</option>")).to_equal(true)
```

</details>

#### renders markdown image attachment blocks with GUI metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 11, kind: "embed", from_line: 0, to_line: 0, content: "![Diagram](assets/diagram.png)", rendered_lines: ["![Diagram](assets/diagram.png)"], status: "ok")
val rendered = gui_render_markdown_block(block)
expect(rendered.html.contains("class=\"md-embed md-embed-image\"")).to_equal(true)
expect(rendered.html.contains("data-embed-kind=\"image\"")).to_equal(true)
expect(rendered.html.contains("data-target=\"assets/diagram.png\"")).to_equal(true)
expect(rendered.html.contains("<img class=\"md-embed-image-preview\" src=\"assets/diagram.png\" alt=\"Diagram\" loading=\"lazy\">")).to_equal(true)
expect(rendered.html.contains("Diagram")).to_equal(true)
expect(rendered.html.contains("![Diagram]")).to_equal(false)
```

</details>

#### renders inline markdown images inside mixed paragraph content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 111, kind: "paragraph", from_line: 0, to_line: 0, content: "Before ![Diagram](assets/diagram.png) after <safe>", rendered_lines: ["Before ![Diagram](assets/diagram.png) after <safe>"], status: "ok")
val rendered = gui_render_markdown_block(block)
expect(rendered.html.contains("Before ")).to_equal(true)
expect(rendered.html.contains("class=\"md-inline-image\"")).to_equal(true)
expect(rendered.html.contains("class=\"md-inline-image-preview\" src=\"assets/diagram.png\" alt=\"Diagram\" loading=\"lazy\"")).to_equal(true)
expect(rendered.html.contains(" after &lt;safe&gt;")).to_equal(true)
expect(rendered.html.contains("![Diagram]")).to_equal(false)
```

</details>

#### renders markdown tables as structured GUI table cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 12, kind: "table", from_line: 0, to_line: 2, content: "| A | B |\n|---|---|\n| 1 | 2 |", rendered_lines: ["| A | B |", "|---|---|", "| 1 | 2 |"], status: "ok")
val rendered = gui_render_markdown_block(block)
expect(rendered.html.contains("class=\"md-table-editor\"")).to_equal(true)
expect(rendered.html.contains("data-event=\"table-row-insert\"")).to_equal(true)
expect(rendered.html.contains("data-event=\"table-column-insert\"")).to_equal(true)
expect(rendered.html.contains("class=\"md-table\"")).to_equal(true)
expect(rendered.html.contains(">A</th>")).to_equal(true)
expect(rendered.html.contains(">B</th>")).to_equal(true)
expect(rendered.html.contains("data-line=\"2\" data-col=\"0\"")).to_equal(true)
expect(rendered.html.contains(">1</td>")).to_equal(true)
expect(rendered.html.contains(">2</td>")).to_equal(true)
expect(rendered.html.contains("---")).to_equal(false)
```

</details>

#### renders markdown task list items as GUI checkboxes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 13, kind: "list", from_line: 4, to_line: 5, content: "- [ ] Todo\n- [x] Done", rendered_lines: ["- [ ] Todo", "- [x] Done"], status: "ok")
val rendered = gui_render_markdown_block(block)
expect(rendered.html.contains("class=\"md-task\"")).to_equal(true)
expect(rendered.html.contains("class=\"md-task checked\"")).to_equal(true)
expect(rendered.html.contains("class=\"md-task-checkbox\"")).to_equal(true)
expect(rendered.html.contains("data-line=\"4\"")).to_equal(true)
expect(rendered.html.contains("data-line=\"5\"")).to_equal(true)
expect(rendered.html.contains("Todo")).to_equal(true)
expect(rendered.html.contains("Done")).to_equal(true)
expect(rendered.html.contains("[ ]")).to_equal(false)
```

</details>

#### renders markdown links with GUI hit-test metadata

1. var buffer = EditorBuffer from text
2. buffer path = editor gui tmp path
3. buffer move cursor
   - Expected: html contains `class="md-link"`
   - Expected: html contains `data-line="1"`
   - Expected: html contains `data-col="4"`
   - Expected: html contains `data-target="target.md"`
   - Expected: html contains `data-target="Wiki Note"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "Title\nSee [Target](target.md) and [[Wiki Note]]\n")
buffer.path = editor_gui_tmp_path("gui_link_source.md")
buffer.move_cursor(0, 0)
val html = gui_render_editor_area(buffer, "markdown", buffer.viewport)
expect(html.contains("class=\"md-link\"")).to_equal(true)
expect(html.contains("data-line=\"1\"")).to_equal(true)
expect(html.contains("data-col=\"4\"")).to_equal(true)
expect(html.contains("data-target=\"target.md\"")).to_equal(true)
expect(html.contains("data-target=\"Wiki Note\"")).to_equal(true)
```

</details>

#### opens markdown links from GUI click events

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. state = gui shell handle event
   - Expected: state.ctrl.session.active_document().path() equals `target_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_path = editor_gui_tmp_path("simple_gui_click_source.md")
val target_path = editor_gui_tmp_path("target.md")
expect(rt_file_write_text(source_path, "See [Target](target.md)\n")).to_equal(true)
expect(rt_file_write_text(target_path, "# Target\n")).to_equal(true)
var session = EditSession.new()
session.open_file(source_path)
var state = gui_shell_new(session)

state = gui_shell_handle_event(state, "link-click", "target.md")

expect(state.ctrl.session.active_document().path()).to_equal(target_path)
```

</details>

#### opens markdown links from GUI ctrl-click cursor hit testing

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. state = gui shell handle event
   - Expected: state.ctrl.session.active_document().path() equals `target_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_path = editor_gui_tmp_path("simple_gui_ctrl_click_source.md")
val target_path = editor_gui_tmp_path("simple_gui_ctrl_click_target.md")
expect(rt_file_write_text(source_path, "See [Target](simple_gui_ctrl_click_target.md)\n")).to_equal(true)
expect(rt_file_write_text(target_path, "# Target\n")).to_equal(true)
var session = EditSession.new()
session.open_file(source_path)
var state = gui_shell_new(session)

state = gui_shell_handle_event(state, "editor-ctrl-click", "0,6")

expect(state.ctrl.session.active_document().path()).to_equal(target_path)
```

</details>

#### toggles markdown task checkboxes from GUI task events

1. var session = EditSession new
   - Expected: rt_file_write_text(path, "- [ ] Todo\n- [x] Done\n") is true
2. session open file
3. var state = gui shell new
4. state = gui shell handle event
   - Expected: state.ctrl.session.active_buffer().line_at(0) equals `- [x] Todo`
5. state = gui shell handle event
   - Expected: state.ctrl.session.active_buffer().line_at(1) equals `- [ ] Done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = EditSession.new()
val path = editor_gui_tmp_path("simple_gui_task_toggle.md")
expect(rt_file_write_text(path, "- [ ] Todo\n- [x] Done\n")).to_equal(true)
session.open_file(path)
var state = gui_shell_new(session)

state = gui_shell_handle_event(state, "task-toggle", "0")
expect(state.ctrl.session.active_buffer().line_at(0)).to_equal("- [x] Todo")

state = gui_shell_handle_event(state, "task-toggle", "1")
expect(state.ctrl.session.active_buffer().line_at(1)).to_equal("- [ ] Done")
```

</details>

#### filters and batches markdown tasks from GUI task controls

1. var session = EditSession new
   - Expected: rt_file_write_text(path, "- [ ] Todo\n- [ ] Review notes\n- [x] Done\n") is true
2. session open file
3. var state = gui shell new
4. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `wiki tasks: done`
   - Expected: state.ctrl.wiki_panel.rows.len() equals `1`
   - Expected: frame.editor_html contains `class="task-query"`
   - Expected: frame.editor_html contains `data-event="task-query"`
   - Expected: frame.editor_html contains `class="task-count"`
5. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `wiki tasks: all`
6. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `wiki tasks: all`
   - Expected: state.ctrl.wiki_task_query equals `review`
   - Expected: state.ctrl.wiki_panel.rows.len() equals `1`
   - Expected: state.ctrl.wiki_panel.rows[0].label equals `Review notes`
7. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `tasks marked done`
   - Expected: state.ctrl.session.active_buffer().line_at(0) equals `- [x] Todo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = EditSession.new()
val path = editor_gui_tmp_path("simple_gui_task_batch.md")
expect(rt_file_write_text(path, "- [ ] Todo\n- [ ] Review notes\n- [x] Done\n")).to_equal(true)
session.open_file(path)
var state = gui_shell_new(session)
state = gui_shell_handle_event(state, "task-filter", "done")
expect(state.ctrl.status_msg).to_equal("wiki tasks: done")
expect(state.ctrl.wiki_panel.rows.len()).to_equal(1)
val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("class=\"task-query\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"task-query\"")).to_equal(true)
expect(frame.editor_html.contains("class=\"task-count\"")).to_equal(true)
state = gui_shell_handle_event(state, "task-filter", "all")
expect(state.ctrl.status_msg).to_equal("wiki tasks: all")
state = gui_shell_handle_event(state, "task-query", "review")
expect(state.ctrl.status_msg).to_equal("wiki tasks: all")
expect(state.ctrl.wiki_task_query).to_equal("review")
expect(state.ctrl.wiki_panel.rows.len()).to_equal(1)
expect(state.ctrl.wiki_panel.rows[0].label).to_equal("Review notes")
state = gui_shell_handle_event(state, "task-batch", "done")
expect(state.ctrl.status_msg).to_equal("tasks marked done")
expect(state.ctrl.session.active_buffer().line_at(0)).to_equal("- [x] Todo")
```

</details>

#### filters vault search results from GUI search controls

1. var root = editor gui tmp path
2. root = editor gui tmp path
   - Expected: rt_dir_create_all(root + "/Projects") is true
   - Expected: rt_file_write_text(path, "# Cache\n- cache task\nbody cache\n") is true
   - Expected: rt_file_write_text(project_path, "# Project Cache\nproject body\n") is true
3. var session = EditSession new
4. var state = gui shell new
   - Expected: frame.editor_html contains `vault-search-tools`
   - Expected: frame.editor_html contains `data-event="vault-search-filter"`
   - Expected: frame.editor_html contains `data-event="vault-search-path-filter"`
5. state = gui shell handle event
   - Expected: state.ctrl.wiki_vault_search_query equals `kind:heading cache`
   - Expected: state.ctrl.wiki_panel.rows.len() equals `2`
   - Expected: state.ctrl.wiki_panel.rows[0].label equals `# Cache`
6. state = gui shell handle event
   - Expected: state.ctrl.wiki_vault_search_query equals `path:Projects kind:heading cache`
   - Expected: state.ctrl.wiki_panel.rows.len() equals `1`
   - Expected: state.ctrl.wiki_panel.rows[0].path equals `project_path`
7. state = gui shell handle event
   - Expected: state.ctrl.wiki_vault_search_query equals `path:Projects cache`
   - Expected: state.ctrl.wiki_panel.rows.len() equals `1`
   - Expected: state.ctrl.wiki_panel.rows[0].path equals `project_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var suffix = 0
var root = editor_gui_tmp_path("simple_gui_vault_search")
while rt_file_exists(root + "/Alpha.md") or rt_file_exists(root + "/Projects/Project.md"):
    suffix = suffix + 1
    root = editor_gui_tmp_path("simple_gui_vault_search_") + suffix.to_text()
expect(rt_dir_create_all(root + "/Projects")).to_equal(true)
val path = root + "/Alpha.md"
val project_path = root + "/Projects/Project.md"
expect(rt_file_write_text(path, "# Cache\n- cache task\nbody cache\n")).to_equal(true)
expect(rt_file_write_text(project_path, "# Project Cache\nproject body\n")).to_equal(true)
var session = EditSession.new()
var state = gui_shell_new(session)
var ctrl = state.ctrl
val searched = ctrl._execute_palette_command("wiki-vault-search", root + "|cache")
ctrl.status_msg = searched.status_msg
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("vault-search-tools")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"vault-search-filter\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"vault-search-path-filter\"")).to_equal(true)

state = gui_shell_handle_event(state, "vault-search-filter", "heading")
expect(state.ctrl.wiki_vault_search_query).to_equal("kind:heading cache")
expect(state.ctrl.wiki_panel.rows.len()).to_equal(2)
expect(state.ctrl.wiki_panel.rows[0].label).to_equal("# Cache")

state = gui_shell_handle_event(state, "vault-search-path-filter", "Projects")
expect(state.ctrl.wiki_vault_search_query).to_equal("path:Projects kind:heading cache")
expect(state.ctrl.wiki_panel.rows.len()).to_equal(1)
expect(state.ctrl.wiki_panel.rows[0].path).to_equal(project_path)

state = gui_shell_handle_event(state, "vault-search-filter", "all")
expect(state.ctrl.wiki_vault_search_query).to_equal("path:Projects cache")
expect(state.ctrl.wiki_panel.rows.len()).to_equal(1)
expect(state.ctrl.wiki_panel.rows[0].path).to_equal(project_path)
```

</details>

#### renders and filters the quick switch picker from GUI controls

1. var session = EditSession new
   - Expected: rt_file_write_text(alpha_path, "# Alpha\n") is true
   - Expected: rt_file_write_text(beta_path, "# Beta\n\n") is true
2. session open file
3. session open file
4. var beta buffer = session active buffer
5. beta buffer move cursor
6. session update active buffer
7. var state = gui shell new
   - Expected: frame.editor_html contains `quick-switch-tools`
   - Expected: frame.editor_html contains `data-event="quick-switch-filter"`
   - Expected: frame.editor_html contains `data-event="quick-switch-insert"`
   - Expected: frame.editor_html contains `2 notes`
8. state = gui shell handle event
   - Expected: state.ctrl.wiki_quick_switch_query equals `beta`
   - Expected: state.ctrl.wiki_panel.rows.len() equals `1`
   - Expected: state.ctrl.wiki_panel.rows[0].path equals `beta_path`
9. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `inserted embed: simple_gui_quick_switch_beta`
   - Expected: state.ctrl.session.active_buffer().to_text() equals `# Beta\n![[simple_gui_quick_switch_beta]]\n\n`
10. state = gui shell handle event
   - Expected: state.ctrl.wiki_quick_switch_query equals ``
   - Expected: state.ctrl.wiki_panel.rows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = EditSession.new()
val alpha_path = editor_gui_tmp_path("simple_gui_quick_switch_alpha.md")
val beta_path = editor_gui_tmp_path("simple_gui_quick_switch_beta.md")
expect(rt_file_write_text(alpha_path, "# Alpha\n")).to_equal(true)
expect(rt_file_write_text(beta_path, "# Beta\n\n")).to_equal(true)
session.open_file(alpha_path)
session.open_file(beta_path)
var beta_buffer = session.active_buffer()
beta_buffer.move_cursor(1, 0)
session.update_active_buffer(beta_buffer)
var state = gui_shell_new(session)
var ctrl = state.ctrl
val opened = ctrl._execute_palette_command("wiki-quick-switch", "")
ctrl.status_msg = opened.status_msg
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("quick-switch-tools")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"quick-switch-filter\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"quick-switch-insert\"")).to_equal(true)
expect(frame.editor_html.contains("2 notes")).to_equal(true)

state = gui_shell_handle_event(state, "quick-switch-filter", "beta")
expect(state.ctrl.wiki_quick_switch_query).to_equal("beta")
expect(state.ctrl.wiki_panel.rows.len()).to_equal(1)
expect(state.ctrl.wiki_panel.rows[0].path).to_equal(beta_path)
state = gui_shell_handle_event(state, "quick-switch-insert", state.ctrl.wiki_panel.rows[0].detail)
expect(state.ctrl.status_msg).to_equal("inserted embed: simple_gui_quick_switch_beta")
expect(state.ctrl.session.active_buffer().to_text()).to_equal("# Beta\n![[simple_gui_quick_switch_beta]]\n\n")

state = gui_shell_handle_event(state, "quick-switch-filter", "")
expect(state.ctrl.wiki_quick_switch_query).to_equal("")
expect(state.ctrl.wiki_panel.rows.len()).to_equal(2)
```

</details>

#### renders and submits the daily note date picker from GUI controls

1. var session = EditSession new
2. var state = gui shell new
   - Expected: frame.editor_html contains `daily-note-tools`
   - Expected: frame.editor_html contains `type="date"`
   - Expected: frame.editor_html contains `data-event="daily-note-create"`
   - Expected: frame.editor_html contains `value="2026-05-20"`
   - Expected: frame.editor_html contains `data-folder="" + daily_root + ""`
3. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `created daily note: " + daily_root + "/2026-05-21-daily.md`
   - Expected: state.ctrl.session.active_document().path() equals `daily_root + "/2026-05-21-daily.md"`
   - Expected: rt_file_read_text(daily_root + "/2026-05-21-daily.md") equals `# 2026-05-21-daily\nDate: 2026-05-21\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val daily_root = editor_gui_tmp_path("simple_gui_daily_note_picker")
expect(rt_dir_create_all(daily_root)).to_equal(true)
var session = EditSession.new()
var state = gui_shell_new(session)
var ctrl = state.ctrl
val opened = ctrl._execute_palette_command("daily-note-picker", "2026-05-20|" + daily_root + "|# {{title}}\nDate: {{date}}\n|{{date}}-daily|md")
ctrl.status_msg = opened.status_msg
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("daily-note-tools")).to_equal(true)
expect(frame.editor_html.contains("type=\"date\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"daily-note-create\"")).to_equal(true)
expect(frame.editor_html.contains("value=\"2026-05-20\"")).to_equal(true)
expect(frame.editor_html.contains("data-folder=\"" + daily_root + "\"")).to_equal(true)

state = gui_shell_handle_event(state, "daily-note-create", "2026-05-21|" + daily_root + "|# {{title}}\nDate: {{date}}\n|{{date}}-daily|md")

expect(state.ctrl.status_msg).to_equal("created daily note: " + daily_root + "/2026-05-21-daily.md")
expect(state.ctrl.session.active_document().path()).to_equal(daily_root + "/2026-05-21-daily.md")
expect(rt_file_read_text(daily_root + "/2026-05-21-daily.md")).to_equal("# 2026-05-21-daily\nDate: 2026-05-21\n")
```

</details>

#### renders filters and submits the template picker variable form from GUI controls

1. var session = EditSession new
2. var state = gui shell new
   - Expected: frame.editor_html contains `template-tools`
   - Expected: frame.editor_html contains `class="template-query"`
   - Expected: frame.editor_html contains `class="template-title"`
   - Expected: frame.editor_html contains `class="template-date"`
   - Expected: frame.editor_html contains `data-event="template-picker-filter"`
   - Expected: frame.editor_html contains `data-event="template-insert"`
   - Expected: frame.editor_html contains `2 templates`
3. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `templates: 1`
   - Expected: state.ctrl.wiki_template_query equals `review`
   - Expected: state.ctrl.wiki_panel.rows[0].label equals `Review.md`
4. state = gui shell handle event
   - Expected: state.ctrl.status_msg contains `inserted template: `
   - Expected: rt_file_read_text(target_path) contains `# Review`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl_root = editor_gui_tmp_path("simple_gui_template_picker")
val target_path = editor_gui_tmp_path("simple_gui_template_picker_target.md")
expect(rt_dir_create_all(tpl_root + "/nested")).to_equal(true)
expect(rt_file_write_text(tpl_root + "/Meeting.md", "## {{title}}\nDate: {{date}}\n")).to_equal(true)
expect(rt_file_write_text(tpl_root + "/nested/Review.md", "# {{title}}\n")).to_equal(true)
expect(rt_file_write_text(target_path, "# Target\n")).to_equal(true)
var session = EditSession.new()
var state = gui_shell_new(session)
var ctrl = state.ctrl
val opened = ctrl._execute_palette_command("template-picker", tpl_root + "|" + target_path + "|Planning|2026-05-22|")
ctrl.status_msg = opened.status_msg
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("template-tools")).to_equal(true)
expect(frame.editor_html.contains("class=\"template-query\"")).to_equal(true)
expect(frame.editor_html.contains("class=\"template-title\"")).to_equal(true)
expect(frame.editor_html.contains("class=\"template-date\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"template-picker-filter\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"template-insert\"")).to_equal(true)
expect(frame.editor_html.contains("2 templates")).to_equal(true)

state = gui_shell_handle_event(state, "template-picker-filter", tpl_root + "|" + target_path + "|Review|2026-05-23|review")
expect(state.ctrl.status_msg).to_equal("templates: 1")
expect(state.ctrl.wiki_template_query).to_equal("review")
expect(state.ctrl.wiki_panel.rows[0].label).to_equal("Review.md")

state = gui_shell_handle_event(state, "template-insert", state.ctrl.wiki_panel.rows[0].detail)
expect(state.ctrl.status_msg.contains("inserted template: ")).to_equal(true)
expect(rt_file_read_text(target_path).contains("# Review")).to_equal(true)
```

</details>

#### renders filters and submits the attachment picker target controls from GUI events

1. var session = EditSession new
2. var state = gui shell new
   - Expected: frame.editor_html contains `attachment-tools`
   - Expected: frame.editor_html contains `class="attachment-query"`
   - Expected: frame.editor_html contains `class="attachment-target"`
   - Expected: frame.editor_html contains `class="attachment-storage"`
   - Expected: frame.editor_html contains `data-event="attachment-picker-filter"`
   - Expected: frame.editor_html contains `data-event="attachment-insert"`
   - Expected: frame.editor_html contains `2 attachments`
3. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `attachments: 1`
   - Expected: state.ctrl.wiki_attachment_query equals `screen`
   - Expected: state.ctrl.wiki_panel.rows[0].label equals `screenshot.png`
4. state = gui shell handle event
   - Expected: state.ctrl.status_msg contains `inserted attachment: attachments/screenshot`
   - Expected: rt_file_read_text(target_path) contains `![screenshot.png](attachments/screenshot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attachment_root = editor_gui_tmp_path("simple_gui_attachment_picker")
val target_path = editor_gui_tmp_path("simple_gui_attachment_picker_target.md")
expect(rt_dir_create_all(attachment_root + "/assets")).to_equal(true)
expect(rt_file_write_text(attachment_root + "/assets/screenshot.png", "png")).to_equal(true)
expect(rt_file_write_text(attachment_root + "/assets/diagram.svg", "svg")).to_equal(true)
expect(rt_file_write_text(target_path, "# Target\n")).to_equal(true)
var session = EditSession.new()
var state = gui_shell_new(session)
var ctrl = state.ctrl
val opened = ctrl._execute_palette_command("attachment-picker", attachment_root + "||" + target_path + "|attachments")
ctrl.status_msg = opened.status_msg
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("attachment-tools")).to_equal(true)
expect(frame.editor_html.contains("class=\"attachment-query\"")).to_equal(true)
expect(frame.editor_html.contains("class=\"attachment-target\"")).to_equal(true)
expect(frame.editor_html.contains("class=\"attachment-storage\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"attachment-picker-filter\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"attachment-insert\"")).to_equal(true)
expect(frame.editor_html.contains("2 attachments")).to_equal(true)

state = gui_shell_handle_event(state, "attachment-picker-filter", attachment_root + "|screen|" + target_path + "|attachments")
expect(state.ctrl.status_msg).to_equal("attachments: 1")
expect(state.ctrl.wiki_attachment_query).to_equal("screen")
expect(state.ctrl.wiki_panel.rows[0].label).to_equal("screenshot.png")

state = gui_shell_handle_event(state, "attachment-insert", state.ctrl.wiki_panel.rows[0].detail)
expect(state.ctrl.status_msg.contains("inserted attachment: attachments/screenshot")).to_equal(true)
expect(rt_file_read_text(target_path).contains("![screenshot.png](attachments/screenshot")).to_equal(true)
```

</details>

#### filters and groups Problems panel rows from GUI controls

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. EditorDiagnostic
5. EditorDiagnostic
6. EditorDiagnostic
   - Expected: frame.editor_html contains `diagnostics-tools`
   - Expected: frame.editor_html contains `diagnostics-table`
   - Expected: frame.editor_html contains `<th>Severity</th>`
   - Expected: frame.editor_html contains `class="diagnostics-message"`
   - Expected: frame.editor_html contains `class="diagnostics-source"`
   - Expected: frame.editor_html contains `simple_gui_problem_filter_first.spl`
   - Expected: frame.editor_html contains `data-event="diagnostics-filter"`
   - Expected: frame.editor_html contains `data-event="diagnostics-group"`
   - Expected: frame.editor_html contains `data-event="diagnostics-sort"`
7. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `problems: 2`
   - Expected: state.ctrl.diagnostics_panel.title equals `Problems (error)`
   - Expected: state.ctrl.diagnostics_panel.rows[0].label equals `simple error`
8. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `problems: 3`
   - Expected: state.ctrl.diagnostics_panel.title equals `Problems grouped by source`
   - Expected: state.ctrl.diagnostics_panel.rows[0].label equals `lint`
   - Expected: state.ctrl.diagnostics_panel.rows[3].label equals `simple`
9. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `problems: 3`
   - Expected: state.ctrl.diagnostics_panel.title equals `Problems sorted by severity`
   - Expected: state.ctrl.diagnostics_panel.rows[0].label equals `simple error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first_path = editor_gui_tmp_path("simple_gui_problem_filter_first.spl")
val second_path = editor_gui_tmp_path("simple_gui_problem_filter_second.spl")
expect(rt_file_write_text(first_path, "fn first():\n    return\n")).to_equal(true)
expect(rt_file_write_text(second_path, "fn second():\n    return\n")).to_equal(true)
var session = EditSession.new()
session.open_file(first_path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.diagnostic_store.set_diagnostics(first_path, [
    EditorDiagnostic(path: first_path, line: 0, col: 3, end_line: 0, end_col: 8, severity: "warning", message: "lint warning", source: "lint"),
    EditorDiagnostic(path: first_path, line: 1, col: 4, end_line: 1, end_col: 8, severity: "error", message: "simple error", source: "simple")
])
ctrl.diagnostic_store.set_diagnostics(second_path, [
    EditorDiagnostic(path: second_path, line: 1, col: 2, end_line: 1, end_col: 5, severity: "error", message: "lint error", source: "lint")
])
val shown = ctrl._execute_palette_command("problems", "")
ctrl.status_msg = shown.status_msg
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("diagnostics-tools")).to_equal(true)
expect(frame.editor_html.contains("diagnostics-table")).to_equal(true)
expect(frame.editor_html.contains("<th>Severity</th>")).to_equal(true)
expect(frame.editor_html.contains("class=\"diagnostics-message\"")).to_equal(true)
expect(frame.editor_html.contains("class=\"diagnostics-source\"")).to_equal(true)
expect(frame.editor_html.contains("simple_gui_problem_filter_first.spl")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"diagnostics-filter\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"diagnostics-group\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"diagnostics-sort\"")).to_equal(true)

state = gui_shell_handle_event(state, "diagnostics-filter", "error|")
expect(state.ctrl.status_msg).to_equal("problems: 2")
expect(state.ctrl.diagnostics_panel.title).to_equal("Problems (error)")
expect(state.ctrl.diagnostics_panel.rows[0].label).to_equal("simple error")

state = gui_shell_handle_event(state, "diagnostics-group", "source")
expect(state.ctrl.status_msg).to_equal("problems: 3")
expect(state.ctrl.diagnostics_panel.title).to_equal("Problems grouped by source")
expect(state.ctrl.diagnostics_panel.rows[0].label).to_equal("lint")
expect(state.ctrl.diagnostics_panel.rows[3].label).to_equal("simple")

state = gui_shell_handle_event(state, "diagnostics-sort", "severity")
expect(state.ctrl.status_msg).to_equal("problems: 3")
expect(state.ctrl.diagnostics_panel.title).to_equal("Problems sorted by severity")
expect(state.ctrl.diagnostics_panel.rows[0].label).to_equal("simple error")
```

</details>

#### renders WorkspaceEdit preview controls in the LSP panel

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. ctrl  show workspace edit preview
   - Expected: frame.editor_html contains `workspace-edit-tools`
   - Expected: frame.editor_html contains `data-event="workspace-edit-confirm"`
   - Expected: frame.editor_html contains `data-event="workspace-edit-cancel"`
   - Expected: frame.editor_html contains `workspace-edit-diff`
   - Expected: frame.editor_html contains `diff-before`
   - Expected: frame.editor_html contains `line 2:1-2:9`
   - Expected: frame.editor_html contains `diff-after`
   - Expected: frame.editor_html contains `    return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_gui_tmp_path("simple_gui_workspace_edit_tools.spl")
expect(rt_file_write_text(path, "fn main():\n  return\n")).to_equal(true)
var session = EditSession.new()
session.open_file(path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
val edit_json = "[{\"range\":{\"start\":{\"line\":1,\"character\":0},\"end\":{\"line\":1,\"character\":8}},\"newText\":\"    return\"}]"
ctrl._show_workspace_edit_preview(edit_json, "formatting")
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)

expect(frame.editor_html.contains("workspace-edit-tools")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"workspace-edit-confirm\"")).to_equal(true)
expect(frame.editor_html.contains("data-event=\"workspace-edit-cancel\"")).to_equal(true)
expect(frame.editor_html.contains("workspace-edit-diff")).to_equal(true)
expect(frame.editor_html.contains("diff-before")).to_equal(true)
expect(frame.editor_html.contains("line 2:1-2:9")).to_equal(true)
expect(frame.editor_html.contains("diff-after")).to_equal(true)
expect(frame.editor_html.contains("    return")).to_equal(true)
```

</details>

#### renders rename preview conflicts in the LSP panel

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. ctrl  show workspace edit preview
   - Expected: frame.editor_html contains `workspace-edit-diff`
   - Expected: frame.editor_html contains `workspace-edit-conflict`
   - Expected: frame.editor_html contains `Conflict`
   - Expected: frame.editor_html contains `conflict: missing file`
   - Expected: frame.editor_html contains `conflict_answer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_gui_tmp_path("simple_gui_rename_conflict_ui.spl")
val missing_path = editor_gui_tmp_path("simple_gui_rename_conflict_missing/target.spl")
expect(rt_file_write_text(path, "fn main():\n    val answer = 1\n")).to_equal(true)
var session = EditSession.new()
session.open_file(path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
val edit_json = "{\"changes\":{\"file://" + missing_path + "\":[{\"range\":{\"start\":{\"line\":1,\"character\":8},\"end\":{\"line\":1,\"character\":14}},\"newText\":\"conflict_answer\"}]}}"
ctrl._show_workspace_edit_preview(edit_json, "rename")
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)

expect(frame.editor_html.contains("workspace-edit-diff")).to_equal(true)
expect(frame.editor_html.contains("workspace-edit-conflict")).to_equal(true)
expect(frame.editor_html.contains("Conflict")).to_equal(true)
expect(frame.editor_html.contains("conflict: missing file")).to_equal(true)
expect(frame.editor_html.contains("conflict_answer")).to_equal(true)
```

</details>

#### applies and cancels WorkspaceEdit previews from GUI controls

1. var apply session = EditSession new
2. apply session open file
3. var apply state = gui shell new
4. apply ctrl  show workspace edit preview
5. apply state = gui shell handle event
   - Expected: apply_state.ctrl.status_msg equals `applied: formatting`
   - Expected: apply_state.ctrl.pending_workspace_edit_json equals ``
   - Expected: apply_state.ctrl.session.active_buffer().line_at(1) equals `    return`
   - Expected: rt_file_write_text(cancel_path, "fn main():\n  return\n") is true
6. var cancel session = EditSession new
7. cancel session open file
8. var cancel state = gui shell new
9. cancel ctrl  show workspace edit preview
10. cancel state = gui shell handle event
   - Expected: cancel_state.ctrl.status_msg equals `workspace edit cancelled`
   - Expected: cancel_state.ctrl.pending_workspace_edit_json equals ``
   - Expected: cancel_state.ctrl.session.active_buffer().line_at(1) equals `  return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apply_path = editor_gui_tmp_path("simple_gui_workspace_edit_apply.spl")
expect(rt_file_write_text(apply_path, "fn main():\n  return\n")).to_equal(true)
var apply_session = EditSession.new()
apply_session.open_file(apply_path)
var apply_state = gui_shell_new(apply_session)
var apply_ctrl = apply_state.ctrl
val apply_json = "[{\"range\":{\"start\":{\"line\":1,\"character\":0},\"end\":{\"line\":1,\"character\":8}},\"newText\":\"    return\"}]"
apply_ctrl._show_workspace_edit_preview(apply_json, "formatting")
apply_state.ctrl = apply_ctrl

apply_state = gui_shell_handle_event(apply_state, "workspace-edit-confirm", "")

expect(apply_state.ctrl.status_msg).to_equal("applied: formatting")
expect(apply_state.ctrl.pending_workspace_edit_json).to_equal("")
expect(apply_state.ctrl.session.active_buffer().line_at(1)).to_equal("    return")

val cancel_path = editor_gui_tmp_path("simple_gui_workspace_edit_cancel.spl")
expect(rt_file_write_text(cancel_path, "fn main():\n  return\n")).to_equal(true)
var cancel_session = EditSession.new()
cancel_session.open_file(cancel_path)
var cancel_state = gui_shell_new(cancel_session)
var cancel_ctrl = cancel_state.ctrl
val cancel_json = "[{\"range\":{\"start\":{\"line\":1,\"character\":0},\"end\":{\"line\":1,\"character\":8}},\"newText\":\"    return\"}]"
cancel_ctrl._show_workspace_edit_preview(cancel_json, "formatting")
cancel_state.ctrl = cancel_ctrl

cancel_state = gui_shell_handle_event(cancel_state, "workspace-edit-cancel", "")

expect(cancel_state.ctrl.status_msg).to_equal("workspace edit cancelled")
expect(cancel_state.ctrl.pending_workspace_edit_json).to_equal("")
expect(cancel_state.ctrl.session.active_buffer().line_at(1)).to_equal("  return")
```

</details>

#### renders and uses LSP navigation history controls

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. ctrl lsp location stack = [EditorLocation
   - Expected: state.ctrl.lsp_location_stack.len() equals `1`
   - Expected: tools_html contains `lsp-navigation-tools`
   - Expected: tools_html contains `data-event="lsp-back"`
5. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `lsp back: " + first_path + ":2`
   - Expected: state.ctrl.session.active_document().path() equals `first_path`
   - Expected: state.ctrl.session.active_buffer().cursor_row equals `1`
   - Expected: state.ctrl.session.active_buffer().cursor_col equals `4`
   - Expected: state.ctrl.lsp_location_stack.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first_path = editor_gui_tmp_path("simple_gui_lsp_history_first.spl")
val second_path = editor_gui_tmp_path("simple_gui_lsp_history_second.spl")
expect(rt_file_write_text(first_path, "fn first():\n    return\n")).to_equal(true)
expect(rt_file_write_text(second_path, "fn second():\n    return\n")).to_equal(true)
var session = EditSession.new()
session.open_file(second_path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.lsp_location_stack = [EditorLocation(path: first_path, line: 1, col: 4)]
var dock = ctrl.session.dock_layout
dock.right_visible = true
dock.active_right = "lsp-panel"
ctrl.session.dock_layout = dock
state.ctrl = ctrl

expect(state.ctrl.lsp_location_stack.len()).to_equal(1)
val tools_html = gui_render_lsp_navigation_tools_html(state.ctrl)
expect(tools_html.contains("lsp-navigation-tools")).to_equal(true)
expect(tools_html.contains("data-event=\"lsp-back\"")).to_equal(true)

state = gui_shell_handle_event(state, "lsp-back", "")
expect(state.ctrl.status_msg).to_equal("lsp back: " + first_path + ":2")
expect(state.ctrl.session.active_document().path()).to_equal(first_path)
expect(state.ctrl.session.active_buffer().cursor_row).to_equal(1)
expect(state.ctrl.session.active_buffer().cursor_col).to_equal(4)
expect(state.ctrl.lsp_location_stack.len()).to_equal(0)
```

</details>

#### renders and selects LSP result rows from GUI clicks

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. ctrl lsp result panel = lsp result panel from response
   - Expected: rows_html contains `class="lsp-result-row selected"`
   - Expected: rows_html contains `data-event="lsp-result-click"`
   - Expected: rows_html contains `data-row="1"`
5. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `lsp result selected`
   - Expected: state.ctrl.lsp_result_panel.selected equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first_path = editor_gui_tmp_path("simple_gui_lsp_result_first.spl")
val second_path = editor_gui_tmp_path("simple_gui_lsp_result_second.spl")
expect(rt_file_write_text(first_path, "fn first():\n    return\n")).to_equal(true)
expect(rt_file_write_text(second_path, "fn second():\n    return\n")).to_equal(true)
var session = EditSession.new()
session.open_file(first_path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.lsp_result_panel = lsp_result_panel_from_response("references", LspResponse(id: 3, ok: true, result_json: "[{\"uri\":\"file://" + first_path + "\",\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":2}}},{\"uri\":\"file://" + second_path + "\",\"range\":{\"start\":{\"line\":1,\"character\":4},\"end\":{\"line\":1,\"character\":8}}}]", error_text: ""))
var dock = ctrl.session.dock_layout
dock.right_visible = true
dock.active_right = "lsp-panel"
ctrl.session.dock_layout = dock
state.ctrl = ctrl

val rows_html = gui_render_lsp_result_rows_html(state.ctrl.lsp_result_panel)
expect(rows_html.contains("class=\"lsp-result-row selected\"")).to_equal(true)
expect(rows_html.contains("data-event=\"lsp-result-click\"")).to_equal(true)
expect(rows_html.contains("data-row=\"1\"")).to_equal(true)

state = gui_shell_handle_event(state, "lsp-result-click", "1")

expect(state.ctrl.status_msg).to_equal("lsp result selected")
expect(state.ctrl.lsp_result_panel.selected).to_equal(1)
```

</details>

#### renders non-Markdown LSP document symbols in the outline pane

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. rows: [LspResultRow
5. ctrl  apply lsp document symbols outline
   - Expected: frame.editor_html contains `outline-pane`
   - Expected: frame.editor_html contains `main`
   - Expected: state.ctrl.session.dock_layout.active_right equals `md-outline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_gui_tmp_path("simple_gui_simple_outline.spl")
expect(rt_file_write_text(path, "fn main():\n    return\n")).to_equal(true)
var session = EditSession.new()
session.open_file(path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.lsp_result_panel = LspResultPanel(
    title: "Document Symbols",
    rows: [LspResultRow(icon: "symbol", label: "main", detail: path + ":1", path: path, line: 0, col: 3, command_name: "", command_payload: "", depth: 0, expanded: false)],
    selected: 0,
    scroll_offset: 0,
    pending: false,
    request_id: 46
)
ctrl._apply_lsp_document_symbols_outline()
state.ctrl = ctrl

val frame = gui_shell_render_frame(state)

expect(frame.editor_html.contains("outline-pane")).to_equal(true)
expect(frame.editor_html.contains("main")).to_equal(true)
expect(state.ctrl.session.dock_layout.active_right).to_equal("md-outline")
```

</details>

#### renders LSP command argument forms for code lens rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = lsp_result_panel_from_response("code-lens", LspResponse(id: 4, ok: true, result_json: "[{\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":9}},\"command\":{\"title\":\"Run main\",\"command\":\"debug-start\",\"arguments\":[\"simple\"]}}]", error_text: ""))
val html = gui_render_lsp_result_rows_html(panel)
expect(html.contains("lsp-command-form")).to_equal(true)
expect(html.contains("class=\"lsp-command-name\"")).to_equal(true)
expect(html.contains("value=\"debug-start\"")).to_equal(true)
expect(html.contains("class=\"lsp-command-args\"")).to_equal(true)
expect(html.contains("value=\"simple\"")).to_equal(true)
expect(html.contains("data-event=\"code-lens-run\"")).to_equal(true)
expect(html.contains("data-value=\"debug-start|simple\"")).to_equal(true)
```

</details>

#### renders and dispatches Code Actions filter and grouping controls

1. var session = EditSession new
2. var state = gui shell new
3. EditorCodeAction
4. EditorCodeAction
5. code ctrl lsp result panel = code ctrl  code action result panel
   - Expected: html contains `class="code-action-tools"`
   - Expected: html contains `data-event="code-actions-filter"`
   - Expected: html contains `data-event="code-actions-group"`
6. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `code actions grouped: kind`
   - Expected: state.ctrl.lsp_result_panel.rows[0].icon equals `group`
7. var filter state = gui shell new
8. EditorCodeAction
9. EditorCodeAction
10. filter ctrl lsp result panel = filter ctrl  code action result panel
11. filter state = gui shell handle event
   - Expected: filter_state.ctrl.status_msg equals `code actions filtered: source`
   - Expected: filter_state.ctrl.lsp_result_panel.rows[0].label equals `Organize imports`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = EditSession.new()
var state = gui_shell_new(session)
var code_ctrl = state.ctrl
code_ctrl.code_actions = [
    EditorCodeAction(title: "Quick one", kind: "quickfix", edit_json: "{\"line\":0,\"newText\":\"quick\"}", command: ""),
    EditorCodeAction(title: "Organize imports", kind: "source.organizeImports", edit_json: "{\"line\":0,\"newText\":\"source\"}", command: "")
]
code_ctrl.lsp_result_panel = code_ctrl._code_action_result_panel(12)
state.ctrl = code_ctrl
val html = gui_render_lsp_result_rows_html(state.ctrl.lsp_result_panel)
expect(html.contains("class=\"code-action-tools\"")).to_equal(true)
expect(html.contains("data-event=\"code-actions-filter\"")).to_equal(true)
expect(html.contains("data-event=\"code-actions-group\"")).to_equal(true)

state = gui_shell_handle_event(state, "code-actions-group", "kind")
expect(state.ctrl.status_msg).to_equal("code actions grouped: kind")
expect(state.ctrl.lsp_result_panel.rows[0].icon).to_equal("group")

var filter_state = gui_shell_new(session)
var filter_ctrl = filter_state.ctrl
filter_ctrl.code_actions = [
    EditorCodeAction(title: "Quick one", kind: "quickfix", edit_json: "{\"line\":0,\"newText\":\"quick\"}", command: ""),
    EditorCodeAction(title: "Organize imports", kind: "source.organizeImports", edit_json: "{\"line\":0,\"newText\":\"source\"}", command: "")
]
filter_ctrl.lsp_result_panel = filter_ctrl._code_action_result_panel(13)
filter_state.ctrl = filter_ctrl
filter_state = gui_shell_handle_event(filter_state, "code-actions-filter", "source")
expect(filter_state.ctrl.status_msg).to_equal("code actions filtered: source")
expect(filter_state.ctrl.lsp_result_panel.rows[0].label).to_equal("Organize imports")
```

</details>

#### escapes HTML in rendered output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("fn _gui_escape_html(s: text) -> text")).to_equal(true)
expect(src.contains("&lt;")).to_equal(true)
expect(src.contains("&gt;")).to_equal(true)
```

</details>

### editor headless backend — testing

#### defines HeadlessBackend class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/headless_backend.spl")
expect(src.contains("class HeadlessBackend:")).to_equal(true)
expect(src.contains("frames: [HeadlessFrame]")).to_equal(true)
```

</details>

#### has capture_frame, frame_count, last_frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/headless_backend.spl")
expect(src.contains("me capture_frame")).to_equal(true)
expect(src.contains("fn frame_count() -> i64")).to_equal(true)
expect(src.contains("fn last_frame() -> HeadlessFrame")).to_equal(true)
```

</details>

### editor SimpleOS adapter

#### provides SimpleOS platform config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/simpleos_adapter.spl")
expect(src.contains("fn simpleos_editor_config() -> PlatformConfig")).to_equal(true)
expect(src.contains("EditorPlatform.SimpleOS")).to_equal(true)
```

</details>

#### has reduced resource limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/simpleos_adapter.spl")
expect(src.contains("fn simpleos_max_open_files() -> i64")).to_equal(true)
expect(src.contains("32")).to_equal(true)
```

</details>

### editor GUI shell

#### defines GuiShellState struct with controller and GUI config

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("struct GuiShellState:")).to_equal(true)
expect(src.contains("ctrl: EditorController")).to_equal(true)
expect(src.contains("extension_host: ExtensionHost")).to_equal(true)
expect(src.contains("config: GuiBackendConfig")).to_equal(true)
expect(src.contains("platform_config: PlatformConfig")).to_equal(true)
```

</details>

#### has gui_shell_init that activates built-in extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_shell_init(state: GuiShellState)")).to_equal(true)
expect(src.contains("extension_host: ctrl.extension_host")).to_equal(true)
expect(src.contains("activate_language(\"simple\")")).to_equal(true)
expect(src.contains("activate_language(\"markdown\")")).to_equal(true)
```

</details>

#### activates extension language events when GUI opens files

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn _gui_activate_active_language")).to_equal(true)
expect(src.contains("state.ctrl.extension_host.activate_language(doc.language_id)")).to_equal(true)
expect(src.contains("state.ctrl.extension_host.emit_event(\"onDidOpenTextDocument\", doc.path())")).to_equal(true)
expect(src.contains("_gui_activate_active_language(state)")).to_equal(true)
```

</details>

#### has gui_shell_run entry point

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_shell_run(session: EditSession)")).to_equal(true)
expect(src.contains("gui_shell_render_frame(state)")).to_equal(true)
```

</details>

#### has GuiFrame for rendered output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("struct GuiFrame:")).to_equal(true)
expect(src.contains("tab_bar_html: text")).to_equal(true)
expect(src.contains("editor_html: text")).to_equal(true)
```

</details>

#### handle_resize parses width and height from data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn _gui_handle_resize")).to_equal(true)
expect(src.contains("index_of(\",\")")).to_equal(true)
expect(src.contains("initial_width")).to_equal(true)
expect(src.contains("initial_height")).to_equal(true)
```

</details>

#### handle_tab_select selects tab by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn _gui_handle_tab_select")).to_equal(true)
expect(src.contains("select_tab(tab_index)")).to_equal(true)
```

</details>

#### gui_shell_present_frame calls rt_gui_present_html

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("extern fn rt_gui_present_html")).to_equal(true)
expect(src.contains("rt_gui_present_html(html)")).to_equal(true)
```

</details>

#### renders and opens wiki panel rows from GUI click events

1. var session = EditSession new
2. session open file
3. session open file
4. var state = gui shell new
5. WikiPanelRow
   - Expected: gui_src contains `class=\\"wiki-row`
   - Expected: gui_src contains `data-row=\\"`
   - Expected: gui_src contains `data-path=\\"`
6. state = gui shell handle event
   - Expected: state.ctrl.session.active_document().path() equals `source_path`
   - Expected: state.ctrl.status_msg equals `wiki jump: " + source_path + ":1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_path = editor_gui_tmp_path("simple_gui_wiki_source.md")
val target_path = editor_gui_tmp_path("simple_gui_wiki_target.md")
expect(rt_file_write_text(source_path, "[[simple_gui_wiki_target]]\n")).to_equal(true)
expect(rt_file_write_text(target_path, "# Target\n")).to_equal(true)
var session = EditSession.new()
session.open_file(source_path)
session.open_file(target_path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.wiki_panel = wiki_panel_with_rows("Backlinks", [
    WikiPanelRow(icon: "backlink", label: "source", detail: source_path + ":1", path: source_path, line: 0)
])
var dock = ctrl.session.dock_layout
dock.right_visible = true
dock.active_right = "wiki-panel"
ctrl.session.dock_layout = dock
state.ctrl = ctrl

val gui_src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(gui_src.contains("class=\\\"wiki-row")).to_equal(true)
expect(gui_src.contains("data-row=\\\"")).to_equal(true)
expect(gui_src.contains("data-path=\\\"")).to_equal(true)

state = gui_shell_handle_event(state, "wiki-panel-click", "0")
expect(state.ctrl.session.active_document().path()).to_equal(source_path)
expect(state.ctrl.status_msg).to_equal("wiki jump: " + source_path + ":1")
```

</details>

#### renders LSP hover popup HTML near the source position

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = gui_render_lsp_hover_popup_html(LspHoverPopup(visible: true, content: "fn main() <safe>", detail: "line 1:4", line: 0, col: 3))
expect(html.contains("class=\"lsp-hover-popup\"")).to_equal(true)
expect(html.contains("data-line=\"0\"")).to_equal(true)
expect(html.contains("data-col=\"3\"")).to_equal(true)
expect(html.contains("data-event=\"lsp-hover-dismiss\"")).to_equal(true)
expect(html.contains("fn main() &lt;safe&gt;")).to_equal(true)
expect(gui_render_lsp_hover_popup_html(lsp_hover_popup_hidden())).to_equal("")
```

</details>

#### requests and debounces LSP hover from GUI editor hover events

1. var session = EditSession new
2. session open file
3. var state = gui shell new
   - Expected: frame.editor_html contains `data-event="editor-hover"`
   - Expected: frame.editor_html contains `data-value="0,0"`
4. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `hover results`
   - Expected: state.ctrl.session.active_buffer().cursor_row equals `0`
   - Expected: state.ctrl.session.active_buffer().cursor_col equals `3`
5. ctrl hover lsp hover popup = LspHoverPopup
6. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `hover unchanged`
   - Expected: state.ctrl.simple_lsp_state.client.next_id equals `next_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_gui_tmp_path("simple_gui_hover_event.spl")
expect(rt_file_write_text(path, "fn main():\n    return\n")).to_equal(true)
var session = EditSession.new()
session.open_file(path)
var state = gui_shell_new(session)
val frame = gui_shell_render_frame(state)
expect(frame.editor_html.contains("data-event=\"editor-hover\"")).to_equal(true)
expect(frame.editor_html.contains("data-value=\"0,0\"")).to_equal(true)

state = gui_shell_handle_event(state, "editor-hover", "0,3")
expect(state.ctrl.status_msg).to_equal("hover results")
expect(state.ctrl.session.active_buffer().cursor_row).to_equal(0)
expect(state.ctrl.session.active_buffer().cursor_col).to_equal(3)
val next_id = state.ctrl.simple_lsp_state.client.next_id
var ctrl_hover = state.ctrl
ctrl_hover.lsp_hover_popup = LspHoverPopup(visible: true, content: "fn main()", detail: "line 1:4", line: 0, col: 3)
state.ctrl = ctrl_hover
state = gui_shell_handle_event(state, "editor-hover", "0,3")
expect(state.ctrl.status_msg).to_equal("hover unchanged")
expect(state.ctrl.simple_lsp_state.client.next_id).to_equal(next_id)
```

</details>

#### delays configurable GUI LSP hover until the hover threshold elapses

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. state ctrl config = editor config set by key
   - Expected: backend_src contains `data-hover-delay-ms`
   - Expected: shell_src contains `state.ctrl.config.hover_delay_ms`
5. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `hover delayed`
   - Expected: state.ctrl.simple_lsp_state.client.next_id equals `next_id`
6. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `hover results`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_gui_tmp_path("simple_gui_hover_delay_event.spl")
expect(rt_file_write_text(path, "fn main():\n    return\n")).to_equal(true)
var session = EditSession.new()
session.open_file(path)
var state = gui_shell_new(session)
state.ctrl.config = editor_config_set_by_key(state.ctrl.config, "hover_delay_ms", "500")
val backend_src = read_text("src/lib/editor/70.backend/gui_backend.spl")
val shell_src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(backend_src.contains("data-hover-delay-ms")).to_equal(true)
expect(shell_src.contains("state.ctrl.config.hover_delay_ms")).to_equal(true)
val next_id = state.ctrl.simple_lsp_state.client.next_id

state = gui_shell_handle_event(state, "editor-hover", "0,3,100")
expect(state.ctrl.status_msg).to_equal("hover delayed")
expect(state.ctrl.simple_lsp_state.client.next_id).to_equal(next_id)

state = gui_shell_handle_event(state, "editor-hover", "0,3,500")
expect(state.ctrl.status_msg).to_equal("hover results")
```

</details>

#### dismisses LSP hover popup from GUI events

1. var session = EditSession new
2. var state = gui shell new
3. state ctrl lsp hover popup = LspHoverPopup
4. state = gui shell handle event
   - Expected: state.ctrl.lsp_hover_popup.visible is false
   - Expected: state.ctrl.status_msg equals `hover dismissed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = EditSession.new()
var state = gui_shell_new(session)
state.ctrl.lsp_hover_popup = LspHoverPopup(visible: true, content: "fn main()", detail: "line 1:4", line: 0, col: 3)

state = gui_shell_handle_event(state, "lsp-hover-dismiss", "")

expect(state.ctrl.lsp_hover_popup.visible).to_equal(false)
expect(state.ctrl.status_msg).to_equal("hover dismissed")
```

</details>

#### renders and dismisses LSP signature popup from GUI events

1. var session = EditSession new
2. var state = gui shell new
3. LspResultRow
4. LspResultRow
5. ctrl lsp signature popup = LspSignaturePopup
6. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `signature overload 2/2`
   - Expected: state.ctrl.lsp_result_panel.selected equals `1`
   - Expected: state.ctrl.lsp_signature_popup.label equals `add(value: text)`
   - Expected: state.ctrl.lsp_signature_popup.active_parameter equals `value: text`
7. state = gui shell handle event
   - Expected: state.ctrl.lsp_signature_popup.visible is false
   - Expected: state.ctrl.status_msg equals `signature dismissed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = gui_render_lsp_signature_popup_html(LspSignaturePopup(visible: true, label: "add(value: i64) <safe>", detail: "Returns value", active_parameter: "value: i64", line: 1, col: 8))
expect(html.contains("class=\"lsp-signature-popup\"")).to_equal(true)
expect(html.contains("data-event=\"lsp-signature-dismiss\"")).to_equal(true)
expect(html.contains("data-event=\"lsp-signature-prev\"")).to_equal(true)
expect(html.contains("data-event=\"lsp-signature-next\"")).to_equal(true)
expect(html.contains("data-active-parameter=\"value: i64\"")).to_equal(true)
expect(html.contains("class=\"signature-active-parameter\"")).to_equal(true)
expect(html.contains(">value: i64</span>")).to_equal(true)
expect(html.contains("&lt;safe&gt;")).to_equal(true)
expect(gui_render_lsp_signature_popup_html(lsp_signature_popup_hidden())).to_equal("")

var session = EditSession.new()
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.lsp_result_panel = LspResultPanel(
    title: "Signature Help",
    rows: [
        LspResultRow(icon: "signature", label: "add(value: i64)", detail: "Returns value", path: "", line: 0, col: 0, command_name: "", command_payload: "value: i64", depth: 0, expanded: false),
        LspResultRow(icon: "signature", label: "add(value: text)", detail: "Returns text", path: "", line: 0, col: 0, command_name: "", command_payload: "value: text", depth: 0, expanded: false)
    ],
    selected: 0,
    scroll_offset: 0,
    pending: false,
    request_id: 1
)
ctrl.lsp_signature_popup = LspSignaturePopup(visible: true, label: "add(value: i64)", detail: "Returns value", active_parameter: "value: i64", line: 1, col: 8)
state.ctrl = ctrl

state = gui_shell_handle_event(state, "lsp-signature-next", "")

expect(state.ctrl.status_msg).to_equal("signature overload 2/2")
expect(state.ctrl.lsp_result_panel.selected).to_equal(1)
expect(state.ctrl.lsp_signature_popup.label).to_equal("add(value: text)")
expect(state.ctrl.lsp_signature_popup.active_parameter).to_equal("value: text")

state = gui_shell_handle_event(state, "lsp-signature-dismiss", "")

expect(state.ctrl.lsp_signature_popup.visible).to_equal(false)
expect(state.ctrl.status_msg).to_equal("signature dismissed")
```

</details>

#### executes inline code lens commands from GUI events

1. var session = EditSession new
2. var state = gui shell new
3. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `debug adapter: Launch Simple`
   - Expected: state.ctrl.debug_status equals `starting`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = EditSession.new()
var state = gui_shell_new(session)

state = gui_shell_handle_event(state, "code-lens-run", "debug-start|simple")

expect(state.ctrl.status_msg).to_equal("debug adapter: Launch Simple")
expect(state.ctrl.debug_status).to_equal("starting")
```

</details>

#### moves the cursor from GUI inlay hint clicks

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. var buffer = state ctrl session active buffer
5. buffer add inlay hint
6. state ctrl session update active buffer
7. state = gui shell handle event
   - Expected: state.ctrl.session.active_buffer().cursor_row equals `1`
   - Expected: state.ctrl.session.active_buffer().cursor_col equals `14`
   - Expected: state.ctrl.status_msg equals `inlay hint selected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_gui_tmp_path("simple_gui_inlay_hint_click.spl")
expect(rt_file_write_text(path, "fn main():\n    val answer = 1\n")).to_equal(true)
var session = EditSession.new()
session.open_file(path)
var state = gui_shell_new(session)
var buffer = state.ctrl.session.active_buffer()
buffer.add_inlay_hint(1, 14, ": i64")
state.ctrl.session.update_active_buffer(buffer)

state = gui_shell_handle_event(state, "inlay-hint-click", "1,14")

expect(state.ctrl.session.active_buffer().cursor_row).to_equal(1)
expect(state.ctrl.session.active_buffer().cursor_col).to_equal(14)
expect(state.ctrl.status_msg).to_equal("inlay hint selected")
```

</details>

#### renders wiki graph panels as clickable GUI graph nodes

1. var session = EditSession new
2. var state = gui shell new
3. WikiPanelRow
   - Expected: graph_html contains `class="wiki-graph"`
   - Expected: graph_html contains `data-layout="deterministic-grid"`
   - Expected: graph_html contains `class="wiki-graph-node selected"`
   - Expected: graph_html contains `data-event="wiki-panel-click"`
   - Expected: graph_html contains `data-x="12"`
   - Expected: graph_html contains `data-y="12"`
   - Expected: graph_html contains `data-from-x="12"`
   - Expected: graph_html contains `data-to-x="12"`
   - Expected: graph_html contains `source -&gt; Target link resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = EditSession.new()
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.wiki_panel = wiki_panel_with_rows("Graph", [
    WikiPanelRow(icon: "link", label: "Target", detail: "source -> Target link resolved", path: editor_gui_tmp_path("simple_gui_graph_target.md"), line: 0)
])
var dock = ctrl.session.dock_layout
dock.right_visible = true
dock.active_right = "wiki-panel"
ctrl.session.dock_layout = dock
state.ctrl = ctrl

val graph_html = gui_render_wiki_graph_html(state.ctrl.wiki_panel)
expect(graph_html.contains("class=\"wiki-graph\"")).to_equal(true)
expect(graph_html.contains("data-layout=\"deterministic-grid\"")).to_equal(true)
expect(graph_html.contains("class=\"wiki-graph-node selected\"")).to_equal(true)
expect(graph_html.contains("data-event=\"wiki-panel-click\"")).to_equal(true)
expect(graph_html.contains("data-x=\"12\"")).to_equal(true)
expect(graph_html.contains("data-y=\"12\"")).to_equal(true)
expect(graph_html.contains("data-from-x=\"12\"")).to_equal(true)
expect(graph_html.contains("data-to-x=\"12\"")).to_equal(true)
expect(graph_html.contains("source -&gt; Target link resolved")).to_equal(true)
```

</details>

#### submits wiki property form edits through the existing property command

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `property set: status`
   - Expected: state.ctrl.session.active_buffer().to_text() contains `status: done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val note_path = editor_gui_tmp_path("simple_gui_wiki_property.md")
expect(rt_file_write_text(note_path, "---\nstatus: active\n---\n# Note\n")).to_equal(true)
var session = EditSession.new()
session.open_file(note_path)
var state = gui_shell_new(session)
state = gui_shell_handle_event(state, "wiki-property-submit", "status|done")
expect(state.ctrl.status_msg).to_equal("property set: status")
expect(state.ctrl.session.active_buffer().to_text().contains("status: done")).to_equal(true)
```

</details>

#### submits wiki property vault edits through the bulk property command

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `vault property review: 2`
   - Expected: state.ctrl.wiki_panel.title equals `Property Review`
5. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `vault property set: 2`
   - Expected: state.ctrl.session.active_buffer().to_text() contains `status: done`
   - Expected: rt_file_read_text(other_path) contains `status: done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = editor_gui_tmp_path("simple_gui_wiki_property_vault")
expect(rt_dir_create_all(root + "/Projects")).to_equal(true)
val note_path = root + "/Home.md"
val other_path = root + "/Projects/Other.md"
expect(rt_file_write_text(note_path, "---\nstatus: active\n---\n# Note\n")).to_equal(true)
expect(rt_file_write_text(other_path, "# Other\n")).to_equal(true)
var session = EditSession.new()
session.open_file(note_path)
var state = gui_shell_new(session)
state = gui_shell_handle_event(state, "wiki-vault-property-review", root + "|status|done")
expect(state.ctrl.status_msg).to_equal("vault property review: 2")
expect(state.ctrl.wiki_panel.title).to_equal("Property Review")
state = gui_shell_handle_event(state, "wiki-vault-property-submit", root + "|status|done")
expect(state.ctrl.status_msg).to_equal("vault property set: 2")
expect(state.ctrl.session.active_buffer().to_text().contains("status: done")).to_equal(true)
expect(rt_file_read_text(other_path).contains("status: done")).to_equal(true)
```

</details>

#### routes GUI table edit controls through markdown table commands

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. var buffer = state ctrl session active buffer
5. buffer move cursor
6. state ctrl session update active buffer
7. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `table row inserted`
   - Expected: state.ctrl.session.active_buffer().dirty is true
8. buffer = state ctrl session active buffer
9. buffer move cursor
10. state ctrl session update active buffer
11. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `table column inserted`
   - Expected: state.ctrl.session.active_buffer().dirty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val note_path = editor_gui_tmp_path("simple_gui_table_edit.md")
expect(rt_file_write_text(note_path, "| A | B |\n| --- | --- |\n| 1 | 2 |\n")).to_equal(true)
var session = EditSession.new()
session.open_file(note_path)
var state = gui_shell_new(session)
var buffer = state.ctrl.session.active_buffer()
buffer.move_cursor(2, 3)
state.ctrl.session.update_active_buffer(buffer)
state = gui_shell_handle_event(state, "table-row-insert", "")
expect(state.ctrl.status_msg).to_equal("table row inserted")
expect(state.ctrl.session.active_buffer().dirty).to_equal(true)
buffer = state.ctrl.session.active_buffer()
buffer.move_cursor(0, 3)
state.ctrl.session.update_active_buffer(buffer)
state = gui_shell_handle_event(state, "table-column-insert", "")
expect(state.ctrl.status_msg).to_equal("table column inserted")
expect(state.ctrl.session.active_buffer().dirty).to_equal(true)
```

</details>

#### commits GUI table cell edits back to markdown source

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. state = gui shell handle event
   - Expected: state.ctrl.status_msg equals `table cell updated`
   - Expected: state.ctrl.session.active_buffer().to_text() contains `| 1 | updated |`
   - Expected: state.ctrl.session.active_buffer().dirty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val note_path = editor_gui_tmp_path("simple_gui_table_cell_edit.md")
expect(rt_file_write_text(note_path, "| A | B |\n| --- | --- |\n| 1 | 2 |\n")).to_equal(true)
var session = EditSession.new()
session.open_file(note_path)
var state = gui_shell_new(session)
state = gui_shell_handle_event(state, "table-cell-commit", "2|1|updated")
expect(state.ctrl.status_msg).to_equal("table cell updated")
expect(state.ctrl.session.active_buffer().to_text().contains("| 1 | updated |")).to_equal(true)
expect(state.ctrl.session.active_buffer().dirty).to_equal(true)
```

</details>

### editor GUI backend — rendering

#### has gui_render_editor_area for HTML output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("fn gui_render_editor_area(buffer: EditorBuffer, language_id: text, viewport: EditorViewport) -> text")).to_equal(true)
expect(src.contains("editor-area")).to_equal(true)
```

</details>

#### renders source area as an editable GUI surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("contenteditable=\\\"true\\\"")).to_equal(true)
expect(src.contains("data-event=\\\"table-cell-commit\\\"")).to_equal(true)
expect(src.contains("role=\\\"textbox\\\"")).to_equal(true)
expect(src.contains("spellcheck=\\\"false\\\"")).to_equal(true)
expect(src.contains("data-language=\\\"")).to_equal(true)
expect(src.contains("data-line=\\\"")).to_equal(true)
expect(src.contains("data-cursor=\\\"true\\\"")).to_equal(true)
```

</details>

#### renders active source characters with GUI hover column targets

1. var buffer = EditorBuffer from text
2. buffer move cursor
   - Expected: html contains `class="hover-target"`
   - Expected: html contains `data-event="editor-hover"`
   - Expected: html contains `data-value="0,2"`
   - Expected: html contains `data-col="2"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "main\n")
buffer.viewport.height = 1
buffer.move_cursor(0, 2)
val html = gui_render_editor_area(buffer, "simple", buffer.viewport)
expect(html.contains("class=\"hover-target\"")).to_equal(true)
expect(html.contains("data-event=\"editor-hover\"")).to_equal(true)
expect(html.contains("data-value=\"0,2\"")).to_equal(true)
expect(html.contains("data-col=\"2\"")).to_equal(true)
```

</details>

#### renders hover targets inside decorated GUI source lines

1. var selected buffer = EditorBuffer from text
2. selected buffer set selection range
   - Expected: selected_html contains `class="selection-range"`
   - Expected: selected_html contains `data-value="0,2"`
3. var semantic buffer = EditorBuffer from text
4. semantic buffer add semantic token
   - Expected: semantic_html contains `semantic-token-1`
   - Expected: semantic_html contains `data-value="0,2"`
5. var hinted buffer = EditorBuffer from text
6. hinted buffer add inlay hint
   - Expected: hinted_html contains `class="inlay-hint"`
   - Expected: hinted_html contains `data-value="0,2"`
7. var markdown buffer = EditorBuffer from text
8. markdown buffer move cursor
   - Expected: markdown_html contains `class="md-link"`
   - Expected: markdown_html contains `data-event="editor-hover"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var selected_buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "alpha\n")
selected_buffer.viewport.height = 1
selected_buffer.set_selection_range(0, 1, 0, 4)
val selected_html = gui_render_editor_area(selected_buffer, "simple", selected_buffer.viewport)
expect(selected_html.contains("class=\"selection-range\"")).to_equal(true)
expect(selected_html.contains("data-value=\"0,2\"")).to_equal(true)

var semantic_buffer = EditorBuffer.from_text(EditorBufferId(value: 2), "main\n")
semantic_buffer.viewport.height = 1
semantic_buffer.add_semantic_token(0, 0, 4, 1)
val semantic_html = gui_render_editor_area(semantic_buffer, "simple", semantic_buffer.viewport)
expect(semantic_html.contains("semantic-token-1")).to_equal(true)
expect(semantic_html.contains("data-value=\"0,2\"")).to_equal(true)

var hinted_buffer = EditorBuffer.from_text(EditorBufferId(value: 3), "answer\n")
hinted_buffer.viewport.height = 1
hinted_buffer.add_inlay_hint(0, 6, ": i64")
val hinted_html = gui_render_editor_area(hinted_buffer, "simple", hinted_buffer.viewport)
expect(hinted_html.contains("class=\"inlay-hint\"")).to_equal(true)
expect(hinted_html.contains("data-value=\"0,2\"")).to_equal(true)

var markdown_buffer = EditorBuffer.from_text(EditorBufferId(value: 4), "Title\n[[Target]]\n")
markdown_buffer.viewport.height = 2
markdown_buffer.move_cursor(0, 0)
val markdown_html = gui_render_editor_area(markdown_buffer, "markdown", markdown_buffer.viewport)
expect(markdown_html.contains("class=\"md-link\"")).to_equal(true)
expect(markdown_html.contains("data-event=\"editor-hover\"")).to_equal(true)
```

</details>

#### renders diagnostic gutter markers in GUI source lines

1. var buffer = EditorBuffer from text
2. buffer path = editor gui tmp path
3. EditorDiagnostic
   - Expected: html contains `diagnostic-gutter error`
   - Expected: html contains `data-diagnostic="error"`
   - Expected: html contains `>E</span>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "first\nsecond\n")
buffer.path = editor_gui_tmp_path("simple_editor_gui_gutter.spl")
buffer.viewport.height = 3
val html = gui_render_editor_area_with_diagnostics(buffer, "simple", buffer.viewport, buffer.path, [
    EditorDiagnostic(path: buffer.path, line: 1, col: 0, end_line: 1, end_col: 1, severity: "error", message: "bad", source: "test")
])

expect(html.contains("diagnostic-gutter error")).to_equal(true)
expect(html.contains("data-diagnostic=\"error\"")).to_equal(true)
expect(html.contains(">E</span>")).to_equal(true)
```

</details>

#### renders folded headers in GUI source lines

1. var buffer = EditorBuffer from text
   - Expected: open_html contains `foldable-header`
   - Expected: open_html contains `fold-badge-open`
   - Expected: open_html contains `data-event="fold-toggle"`
   - Expected: open_html contains `data-fold-end="1"`
   - Expected: open_html contains `>fold</button>`
2. buffer fold range
   - Expected: html contains `folded-header`
   - Expected: html contains `fold-badge`
   - Expected: html does not contain `fold-badge-open`
   - Expected: html contains `data-event="fold-toggle"`
   - Expected: html contains `data-value="0"`
   - Expected: html contains `+1 folded`
   - Expected: html does not contain `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "# One\nbody\n# Two")
buffer.viewport.height = 3
val open_html = gui_render_editor_area(buffer, "markdown", buffer.viewport)
expect(open_html.contains("foldable-header")).to_equal(true)
expect(open_html.contains("fold-badge-open")).to_equal(true)
expect(open_html.contains("data-event=\"fold-toggle\"")).to_equal(true)
expect(open_html.contains("data-fold-end=\"1\"")).to_equal(true)
expect(open_html.contains(">fold</button>")).to_equal(true)
buffer.fold_range(0, 1)
val html = gui_render_editor_area(buffer, "markdown", buffer.viewport)
expect(html.contains("folded-header")).to_equal(true)
expect(html.contains("fold-badge")).to_equal(true)
expect(html.contains("fold-badge-open")).to_equal(false)
expect(html.contains("data-event=\"fold-toggle\"")).to_equal(true)
expect(html.contains("data-value=\"0\"")).to_equal(true)
expect(html.contains("+1 folded")).to_equal(true)
expect(html.contains("body")).to_equal(false)
```

</details>

#### unfolds folded source ranges from GUI fold badges

1. var session = EditSession new
2. session open file
3. var state = gui shell new
4. var buffer = ctrl session active buffer
5. buffer fold range
6. ctrl session update active buffer
7. state = gui shell handle event
8. buffer = state ctrl session active buffer
   - Expected: buffer.folded_ranges.len() equals `0`
   - Expected: buffer.cursor_row equals `0`
   - Expected: state.ctrl.status_msg equals `unfolded section`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val note_path = editor_gui_tmp_path("simple_gui_fold_badge.md")
expect(rt_file_write_text(note_path, "# One\nbody\n# Two\n")).to_equal(true)
var session = EditSession.new()
session.open_file(note_path)
var state = gui_shell_new(session)
var ctrl = state.ctrl
var buffer = ctrl.session.active_buffer()
buffer.fold_range(0, 1)
ctrl.session.update_active_buffer(buffer)
state.ctrl = ctrl
state = gui_shell_handle_event(state, "fold-toggle", "0")
buffer = state.ctrl.session.active_buffer()
expect(buffer.folded_ranges.len()).to_equal(0)
expect(buffer.cursor_row).to_equal(0)
expect(state.ctrl.status_msg).to_equal("unfolded section")
```

</details>

#### captures folded header markers in headless frames

1. var buffer = EditorBuffer from text
2. buffer fold range
3. var backend = HeadlessBackend new
4. backend capture frame
   - Expected: frame.lines[0] contains `[+1 folded | za]`
   - Expected: frame.lines[1] equals `next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "head\nbody\nnext\n")
buffer.fold_range(0, 1)
var backend = HeadlessBackend.new(40, 5)
backend.capture_frame(buffer, "NORMAL", "")
val frame = backend.last_frame()
expect(frame.lines[0].contains("[+1 folded | za]")).to_equal(true)
expect(frame.lines[1]).to_equal("next")
```

</details>

#### has gui_render_tab_bar_html for tab rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("fn gui_render_tab_bar_html(session: EditSession) -> text")).to_equal(true)
expect(src.contains("tab-bar")).to_equal(true)
```

</details>

#### has gui_render_file_tree_html for tree rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("fn gui_render_file_tree_html(file_tree: FileTreeState) -> text")).to_equal(true)
expect(src.contains("file-tree")).to_equal(true)
```

</details>

### editor main — GUI flag

#### supports --gui flag for GUI mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/main.spl")
expect(src.contains("\"--gui\"")).to_equal(true)
expect(src.contains("gui_shell_run(session)")).to_equal(true)
expect(src.contains("editor_tui_run(session)")).to_equal(true)
```

</details>

### editor MCP tools

#### defines editor_mcp_tools registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/mcp_tools.spl")
expect(src.contains("fn editor_mcp_tools() -> [McpToolDef]")).to_equal(true)
```

</details>

#### registers 8 MCP tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/mcp_tools.spl")
expect(src.contains("editor.open_file")).to_equal(true)
expect(src.contains("editor.read_buffer")).to_equal(true)
expect(src.contains("editor.edit")).to_equal(true)
expect(src.contains("editor.search")).to_equal(true)
expect(src.contains("editor.diagnostics")).to_equal(true)
expect(src.contains("editor.goto_definition")).to_equal(true)
expect(src.contains("editor.list_open_files")).to_equal(true)
expect(src.contains("editor.run_command")).to_equal(true)
```

</details>

#### has editor_mcp_dispatch for tool execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/mcp_tools.spl")
expect(src.contains("fn editor_mcp_dispatch(session: EditSession, tool_name: text, args: [text]) -> McpToolResult")).to_equal(true)
```

</details>

#### dispatches registered navigation MCP tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/mcp_tools.spl")
expect(src.contains("if tool_name == \"editor.goto_definition\"")).to_equal(true)
expect(src.contains("ctrl._request_active_definition()")).to_equal(true)
expect(src.contains("ctrl_cmd._execute_palette_command(args[0], \"\")")).to_equal(true)
```

</details>

#### maps VSCode-style GUI shortcuts to editor IDE actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl") + read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("gui_key == \"Ctrl+Space\"")).to_equal(true)
expect(src.contains("gui_key == \"F12\"")).to_equal(true)
expect(src.contains("gui_key == \"Ctrl+.\"")).to_equal(true)
expect(src.contains("gui_key == \"Shift+Alt+Right\"")).to_equal(true)
expect(src.contains("gui_key == \"Shift+Alt+Left\"")).to_equal(true)
expect(src.contains("gui_key == \"F5\"")).to_equal(true)
expect(src.contains("_request_active_lsp_action(\"completion\")")).to_equal(true)
expect(src.contains("_request_active_lsp_action(\"definition\")")).to_equal(true)
expect(src.contains("_expand_lsp_selection_range()")).to_equal(true)
expect(src.contains("_shrink_lsp_selection_range()")).to_equal(true)
expect(src.contains("_start_debug_adapter(\"simple\")")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_gui_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor platform — detection
- editor config — SDN settings
- editor TUI backend — formalized
- editor GUI backend — Surface integration
- editor headless backend — testing
- editor SimpleOS adapter
- editor GUI shell
- editor GUI backend — rendering
- editor main — GUI flag
- editor MCP tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 80 |
| Active scenarios | 80 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
