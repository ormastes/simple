# Editor Md Wiki Index Specification

> <details>

<!-- sdn-diagram:id=editor_md_wiki_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_md_wiki_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_md_wiki_index_spec -> std
editor_md_wiki_index_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_md_wiki_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Md Wiki Index Specification

## Scenarios

### editor markdown wiki index

#### indexes wiki links backlinks and unresolved links

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = md_wiki_document("vault/Home.md", "---\ntags: project\n---\n# Home\nSee [[Project Alpha|Alpha]] and [[Missing Note]].\n")
val alpha = md_wiki_document("vault/Project Alpha.md", "# Project Alpha\n- [ ] Ship wiki index #project\n- [x] Draft plan\n")
val index = md_wiki_index_documents([home, alpha])

expect(index.documents.len()).to_equal(2)
expect(index.links.len()).to_equal(2)

val backlinks = md_wiki_backlinks(index, "vault/Project Alpha.md")
expect(backlinks.len()).to_equal(1)
expect(backlinks[0].source_path).to_equal("vault/Home.md")
expect(backlinks[0].display).to_equal("Alpha")

val unresolved = md_wiki_unresolved_links(index)
expect(unresolved.len()).to_equal(1)
expect(unresolved[0].target).to_equal("Missing Note")
```

</details>

#### indexes tasks tags properties and quick switch targets

1. md wiki document
2. md wiki document
   - Expected: fuzzy.len() equals `1`
   - Expected: fuzzy[0].path equals `vault/Project Alpha.md`
   - Expected: ranked[0].path equals `vault/Personal Area.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = md_wiki_document("vault/Home.md", "---\ntype: note\nstatus: active\ntags: project\n---\n# Home\n#inbox [[Project Alpha]]\n")
val alpha = md_wiki_document("vault/Project Alpha.md", "# Project Alpha\n- [ ] Ship wiki index #project\n- [x] Draft plan #done\n")
val index = md_wiki_index_documents([home, alpha])

val open_tasks = md_wiki_tasks(index, false)
expect(open_tasks.len()).to_equal(1)
expect(open_tasks[0].text_content).to_equal("Ship wiki index #project")

val done_tasks = md_wiki_tasks(index, true)
expect(done_tasks.len()).to_equal(1)
expect(done_tasks[0].text_content).to_equal("Draft plan #done")
expect(md_wiki_tasks_filtered(index, "all").len()).to_equal(2)
expect(md_wiki_tasks_filtered(index, "done").len()).to_equal(1)
expect(md_wiki_tasks_filtered(index, "open").len()).to_equal(1)

val project_tags = md_wiki_tags(index, "project")
expect(project_tags.len()).to_equal(2)

val props = md_wiki_properties_for_path(index, "vault/Home.md")
expect(props.len()).to_equal(3)
expect(props[0].key).to_equal("type")
expect(props[0].value).to_equal("note")

val quick = md_wiki_quick_switch(index, "alpha")
expect(quick.len()).to_equal(1)
expect(quick[0].path).to_equal("vault/Project Alpha.md")

val fuzzy_docs = md_wiki_index_documents([
    home,
    alpha,
    md_wiki_document("vault/Planning Archive.md", "# Planning Archive\n"),
    md_wiki_document("vault/Personal Area.md", "# Personal Area\n")
])
val fuzzy = md_wiki_quick_switch(fuzzy_docs, "palpha")
expect(fuzzy.len()).to_equal(1)
expect(fuzzy[0].path).to_equal("vault/Project Alpha.md")
val ranked = md_wiki_quick_switch(fuzzy_docs, "personal")
expect(ranked[0].path).to_equal("vault/Personal Area.md")
```

</details>

#### indexes embeds attachments callouts and graph edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = md_wiki_document("vault/Home.md", "# Home\n![[Project Alpha|Alpha embed]]\n![[diagram.png]]\n![Alt](assets/photo.jpg)\n> [!NOTE]- Folded title\n")
val alpha = md_wiki_document("vault/Project Alpha.md", "# Project Alpha\n")
val index = md_wiki_index_documents([home, alpha])

expect(index.embeds.len()).to_equal(2)
expect(index.embeds[0].target).to_equal("Project Alpha")
expect(index.embeds[0].display).to_equal("Alpha embed")
expect(index.embeds[0].resolved).to_equal(true)
expect(md_wiki_unresolved_embeds(index).len()).to_equal(1)

val attachments = md_wiki_attachments(index, "vault/Home.md")
expect(attachments.len()).to_equal(2)
expect(attachments[0].target).to_equal("diagram.png")
expect(attachments[1].target).to_equal("assets/photo.jpg")

val callouts = md_wiki_callouts(index, "")
expect(callouts.len()).to_equal(1)
expect(callouts[0].callout_type).to_equal("note")
expect(callouts[0].title).to_equal("Folded title")
expect(callouts[0].folded).to_equal(true)

val edges = md_wiki_graph_edges(index, "vault/Home.md")
expect(edges.len()).to_equal(2)
expect(edges[0].edge_type).to_equal("embed")
```

</details>

#### builds renderable wiki panels from index query results

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = md_wiki_document("vault/Home.md", "---\nstatus: active\nowner: docs\n---\n# Home\nSee [[Project Alpha|Alpha]].\n#inbox\n")
val alpha = md_wiki_document("vault/Project Alpha.md", "# Project Alpha\n- [ ] Ship #project\n- [x] Done\n")
val index = md_wiki_index_documents([home, alpha])

val backlinks = wiki_panel_from_backlinks(md_wiki_backlinks(index, "vault/Project Alpha.md"))
expect(backlinks.title).to_equal("Backlinks")
expect(backlinks.rows.len()).to_equal(1)
expect(backlinks.rows[0].path).to_equal("vault/Home.md")
expect(wiki_panel_render(backlinks, 5)[0].contains("backlink Alpha")).to_equal(true)

val tasks = wiki_panel_from_tasks(md_wiki_tasks(index, false))
expect(tasks.rows.len()).to_equal(1)
expect(tasks.rows[0].icon).to_equal("open")
expect(tasks.rows[0].label).to_equal("Ship #project")

val tags = wiki_panel_from_tags(md_wiki_tags(index, "project"))
expect(tags.rows.len()).to_equal(1)
expect(tags.rows[0].label).to_equal("#project")

val props = wiki_panel_from_properties(md_wiki_properties_for_path(index, "vault/Home.md"))
expect(props.title).to_equal("Properties")
expect(props.rows.len()).to_equal(2)
expect(props.rows[0].icon).to_equal("property")
expect(props.rows[0].label).to_equal("status")
expect(props.rows[0].detail).to_equal("active")
val fields = wiki_property_form_fields(props)
expect(fields.len()).to_equal(2)
expect(fields[0].key).to_equal("status")
expect(fields[0].value).to_equal("active")
expect(fields[0].payload).to_equal("status|active")
expect(wiki_property_form_render(props, 5)[0].contains("property status = active")).to_equal(true)

val graph = wiki_panel_from_graph_edges(md_wiki_graph_edges(index, "vault/Home.md"))
expect(graph.rows.len()).to_equal(1)
expect(graph.rows[0].icon).to_equal("link")
expect(wiki_panel_target_path(graph)).to_equal("vault/Home.md")
val resolved_graph = wiki_panel_from_graph_edges_with_index(md_wiki_graph_edges(index, "vault/Home.md"), index)
expect(resolved_graph.rows[0].path).to_equal("vault/Project Alpha.md")
expect(resolved_graph.rows[0].detail.contains("vault/Home.md -> Project Alpha link resolved")).to_equal(true)
```

</details>

#### maintains an invalidatable vault search index

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = md_wiki_document("vault/Home.md", "# Home\nAlpha planning note\n")
val alpha = md_wiki_document("vault/Alpha.md", "# Alpha\nShip search cache\n")
val index = md_vault_search_index_new("vault", [home])
expect(index.version).to_equal(1)
expect(index.dirty).to_equal(false)
expect(md_vault_search_index_search(index, "cache").len()).to_equal(0)

val updated = md_vault_search_index_update_document(index, alpha)
expect(updated.version).to_equal(2)
expect(updated.dirty).to_equal(false)
val matches = md_vault_search_index_search(updated, "cache")
expect(matches.len()).to_equal(1)
expect(matches[0].path).to_equal("vault/Alpha.md")
expect(matches[0].score).to_be_greater_than(0)

val invalidated = md_vault_search_index_invalidate(updated)
expect(invalidated.version).to_equal(2)
expect(invalidated.dirty).to_equal(true)
val refreshed = md_vault_search_index_refresh(invalidated, [home])
expect(refreshed.version).to_equal(3)
expect(refreshed.dirty).to_equal(false)
expect(md_vault_search_index_search(refreshed, "cache").len()).to_equal(0)

val removed = md_vault_search_index_remove_document(updated, "vault/Alpha.md")
expect(removed.version).to_equal(3)
expect(md_vault_search_index_search(removed, "cache").len()).to_equal(0)

val changed = md_vault_search_index_apply_file_change(refreshed, "vault/Home.md", "# Home\nCache returns\n", 2)
expect(changed.version).to_equal(4)
expect(changed.dirty).to_equal(false)
expect(md_vault_search_index_search(changed, "cache").len()).to_equal(1)

val watched = md_vault_search_index_apply_watched_changes(changed, ["vault/Home.md"])
expect(watched.version).to_equal(4)
expect(watched.dirty).to_equal(true)

val deleted = md_vault_search_index_apply_file_change(changed, "vault/Home.md", "", 3)
expect(deleted.version).to_equal(5)
expect(md_vault_search_index_search(deleted, "cache").len()).to_equal(0)
```

</details>

#### ranks vault search matches by relevance before path order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paragraph = md_wiki_document("vault/Alpha.md", "# Alpha\ncache body\n")
val heading = md_wiki_document("vault/Zeta.md", "# Cache\nbody\n")
val title = md_wiki_document("vault/Cache Guide.md", "# Guide\nbody cache cache\n")
val results = md_search_vault_documents([paragraph, heading, title], "cache")
expect(results.len()).to_equal(3)
expect(results[0].path).to_equal("vault/Cache Guide.md")
expect(results[0].score).to_be_greater_than(results[1].score)
expect(results[1].path).to_equal("vault/Zeta.md")
expect(results[1].score).to_be_greater_than(results[2].score)
```

</details>

#### filters vault search by path and block kind operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val project = md_wiki_document("vault/Projects/Alpha.md", "# Cache\n- cache task\nbody cache\n")
val archive = md_wiki_document("vault/Archive/Alpha.md", "# Cache\nbody cache\n")
val path_results = md_search_vault_documents([project, archive], "path:Projects cache")
expect(path_results.len()).to_equal(3)
expect(path_results[0].path).to_equal("vault/Projects/Alpha.md")
expect(path_results[1].path).to_equal("vault/Projects/Alpha.md")
expect(path_results[2].path).to_equal("vault/Projects/Alpha.md")

val heading_results = md_search_vault_documents([project, archive], "kind:heading cache")
expect(heading_results.len()).to_equal(2)
expect(heading_results[0].block_kind).to_equal("heading")
expect(heading_results[1].block_kind).to_equal("heading")

val list_results = md_search_vault_documents([project, archive], "block:list cache")
expect(list_results.len()).to_equal(1)
expect(list_results[0].block_kind).to_equal("list")
expect(md_vault_search_query_replace_kind_filter("path:Projects kind:list cache", "heading")).to_equal("kind:heading path:Projects cache")
expect(md_vault_search_query_replace_kind_filter("kind:heading path:Projects cache", "all")).to_equal("path:Projects cache")
expect(md_vault_search_query_replace_path_filter("path:Projects kind:list cache", "Archive")).to_equal("path:Archive kind:list cache")
expect(md_vault_search_query_replace_path_filter("kind:heading path:Projects cache", "all")).to_equal("kind:heading cache")
```

</details>

#### persists and reloads vault search indexes from disk

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_path = "/tmp/simple_editor_vault_search_index.cache"
val home = md_wiki_document("vault/Home.md", "# Home\ncache\twith tab\n")
val guide = md_wiki_document("vault/Cache Guide.md", "# Guide\ncache cache\n")
val index = md_vault_search_index_new("vault", [home, guide])
expect(md_vault_search_index_save(index, cache_path)).to_equal(true)

val loaded = md_vault_search_index_load(cache_path)
expect(loaded.root).to_equal("vault")
expect(loaded.version).to_equal(1)
expect(loaded.dirty).to_equal(false)
expect(loaded.documents.len()).to_equal(2)
expect(loaded.documents[0].content.contains("cache\twith tab")).to_equal(true)
val results = md_vault_search_index_search(loaded, "cache")
expect(results.len()).to_equal(2)
expect(results[0].path).to_equal("vault/Cache Guide.md")
expect(results[0].score).to_be_greater_than(results[1].score)
expect(md_vault_search_index_matches_documents(loaded, [guide, home])).to_equal(true)
expect(md_vault_search_index_matches_documents(loaded, [home])).to_equal(false)
expect(md_vault_search_index_matches_documents(loaded, [md_wiki_document("vault/Home.md", "# Home\nchanged\n"), guide])).to_equal(false)

val missing = md_vault_search_index_load("/tmp/simple_editor_missing_vault_search_index.cache")
expect(missing.dirty).to_equal(true)
expect(missing.documents.len()).to_equal(0)
```

</details>

#### expands templates and computes daily note paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = md_wiki_template("meeting", "# {{title}}\nDate: {{date}}\n")
val rendered = md_wiki_apply_template(tpl, "Planning", "2026-05-13")
expect(rendered).to_equal("# Planning\nDate: 2026-05-13\n")
val custom = md_wiki_apply_template_vars(md_wiki_template("project", "# {{title}}\nOwner: {{owner}}\nStatus: {{status}}\n"), "Planning", "2026-05-13", [md_wiki_template_var("owner", "Docs"), md_wiki_template_var("status", "Active")])
expect(custom).to_equal("# Planning\nOwner: Docs\nStatus: Active\n")

val daily = md_wiki_daily_note_config("Journal/", "# {{title}}\nCreated: {{date}}\n")
expect(md_wiki_daily_note_path(daily, "2026-05-13")).to_equal("Journal/2026-05-13.md")
expect(md_wiki_daily_note_content(daily, "2026-05-13")).to_equal("# 2026-05-13\nCreated: 2026-05-13\n")
val configured_daily = md_wiki_daily_note_config_with_title("Journal/2026", "{{date}}-daily", "markdown", "# {{title}}\n")
expect(md_wiki_daily_note_path(configured_daily, "2026-05-13")).to_equal("Journal/2026/2026-05-13-daily.markdown")
expect(md_wiki_daily_note_content(configured_daily, "2026-05-13")).to_equal("# 2026-05-13-daily\n")
```

</details>

#### exposes wiki index queries through editor MCP tools

1. var session = EditSession new
2. session open file
3. session open file
   - Expected: backlinks.ok is true
   - Expected: backlinks.content contains `home_path`
   - Expected: unresolved.ok is true
   - Expected: unresolved.content contains `Missing`
   - Expected: tags.ok is true
   - Expected: tags.content contains `#project`
   - Expected: props.ok is true
   - Expected: props.content contains `tags: project`
   - Expected: set_prop.ok is true
   - Expected: rt_file_read_text(home_path) contains `status: active`
   - Expected: tasks.ok is true
   - Expected: tasks.content contains `Finish #project`
   - Expected: quick.ok is true
   - Expected: quick.content contains `alpha_path`
   - Expected: created.ok is true
   - Expected: created.content contains `created_path`
   - Expected: rt_file_read_text(created_path) equals `# Created Note\n\n`
   - Expected: embeds.ok is true
   - Expected: embeds.content contains `simple_editor_wiki_alpha`
   - Expected: attachments.ok is true
   - Expected: attachments.content contains `diagram.png`
   - Expected: rt_file_write_text(attachment_target, "# Attachment Target\n") is true
   - Expected: inserted_attachment.ok is true
   - Expected: rt_file_read_text(attachment_target) equals `# Attachment Target\n![Photo](assets/photo.png)\n`
   - Expected: rt_dir_create_all(stored_root + "/incoming") is true
4. rt file delete
5. rt file delete
   - Expected: rt_file_write_text(stored_target, "# Stored Attachment\n") is true
   - Expected: rt_file_write_text(stored_source, "image-bytes") is true
   - Expected: stored_attachment.ok is true
   - Expected: stored_attachment.content contains `assets/image`
   - Expected: rt_file_read_text(stored_target) contains `# Stored Attachment\n![Image](assets/image`
   - Expected: rt_file_write_text(stored_source, "image-bytes-new") is true
   - Expected: renamed_attachment.ok is true
   - Expected: renamed_attachment.content contains `assets/image-`
   - Expected: rt_file_read_text(stored_target) contains `![Image 2](assets/image-`
   - Expected: callouts.ok is true
   - Expected: callouts.content contains `warning`
   - Expected: graph.ok is true
   - Expected: graph.content contains `embed`
   - Expected: tpl_result.ok is true
   - Expected: tpl_result.content contains `# Note`
   - Expected: tpl_custom.ok is true
   - Expected: tpl_custom.content equals `# Note\nOwner: Docs\nStatus: Active\n`
   - Expected: rt_dir_create_all(template_root) is true
   - Expected: rt_file_write_text(tpl_path, "## {{title}}\nDate: {{date}}\n") is true
   - Expected: rt_file_write_text(target_path, "# Target\n") is true
   - Expected: templates.ok is true
   - Expected: templates.content contains `tpl_path`
   - Expected: inserted_template.ok is true
   - Expected: rt_file_read_text(target_path) equals `# Target\n## Planning\nDate: 2026-05-15\n`
   - Expected: rt_file_write_text(custom_tpl_path, "## {{title}}\nOwner: {{owner}}\nStatus: {{status}}\n") is true
   - Expected: rt_file_write_text(custom_target_path, "# Custom Target\n") is true
   - Expected: inserted_custom_template.ok is true
   - Expected: rt_file_read_text(custom_target_path) equals `# Custom Target\n## Project\nOwner: Docs\nStatus: Active\n`
   - Expected: daily.ok is true
   - Expected: daily.content contains `Daily/2026-05-13.md`
   - Expected: configured_daily.ok is true
   - Expected: configured_daily.content contains `Journal/2026/2026-05-13-daily.markdown`
   - Expected: configured_daily.content contains `# 2026-05-13-daily`
   - Expected: rt_dir_create_all(daily_root) is true
   - Expected: created_daily.ok is true
   - Expected: created_daily.content contains `daily_root + "/2026-05-14.md"`
   - Expected: rt_file_read_text(daily_root + "/2026-05-14.md") equals `# 2026-05-14\nCreated: 2026-05-14\n`
   - Expected: rt_dir_create_all(configured_daily_root + "/2026") is true
   - Expected: created_configured_daily.ok is true
   - Expected: created_configured_daily.content contains `configured_daily_root + "/2026/2026-05-14-daily.markdown"`
   - Expected: rt_file_read_text(configured_daily_root + "/2026/2026-05-14-daily.markdown") equals `# 2026-05-14-daily\nCreated: 2026-05-14\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 129 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home_path = "/tmp/simple_editor_wiki_home.md"
val alpha_path = "/tmp/simple_editor_wiki_alpha.md"
expect(rt_file_write_text(home_path, "---\ntags: project\n---\nSee [[simple_editor_wiki_alpha|Alpha]] and [[Missing]].\n![[simple_editor_wiki_alpha|Embed Alpha]]\n![[diagram.png]]\n> [!WARNING] Be careful\n#inbox\n")).to_equal(true)
expect(rt_file_write_text(alpha_path, "# Alpha\n- [ ] Finish #project\n")).to_equal(true)
var session = EditSession.new()
session.open_file(home_path)
session.open_file(alpha_path)

val backlinks = editor_mcp_dispatch(session, "editor.wiki_backlinks", [alpha_path])
expect(backlinks.ok).to_equal(true)
expect(backlinks.content.contains(home_path)).to_equal(true)

val unresolved = editor_mcp_dispatch(session, "editor.wiki_unresolved", [])
expect(unresolved.ok).to_equal(true)
expect(unresolved.content.contains("Missing")).to_equal(true)

val tags = editor_mcp_dispatch(session, "editor.wiki_tags", ["project"])
expect(tags.ok).to_equal(true)
expect(tags.content.contains("#project")).to_equal(true)

val props = editor_mcp_dispatch(session, "editor.wiki_properties", [home_path])
expect(props.ok).to_equal(true)
expect(props.content.contains("tags: project")).to_equal(true)

val set_prop = editor_mcp_dispatch(session, "editor.wiki_set_property", [home_path, "status", "active"])
expect(set_prop.ok).to_equal(true)
expect(rt_file_read_text(home_path).contains("status: active")).to_equal(true)

val tasks = editor_mcp_dispatch(session, "editor.wiki_tasks", ["open"])
expect(tasks.ok).to_equal(true)
expect(tasks.content.contains("Finish #project")).to_equal(true)

val quick = editor_mcp_dispatch(session, "editor.wiki_quick_switch", ["alpha"])
expect(quick.ok).to_equal(true)
expect(quick.content.contains(alpha_path)).to_equal(true)

val created_path = "/tmp/simple_editor_wiki_created.md"
val created = editor_mcp_dispatch(session, "editor.wiki_create_note", [created_path, "Created Note"])
expect(created.ok).to_equal(true)
expect(created.content.contains(created_path)).to_equal(true)
expect(rt_file_read_text(created_path)).to_equal("# Created Note\n\n")

val embeds = editor_mcp_dispatch(session, "editor.wiki_embeds", [home_path])
expect(embeds.ok).to_equal(true)
expect(embeds.content.contains("simple_editor_wiki_alpha")).to_equal(true)

val attachments = editor_mcp_dispatch(session, "editor.wiki_attachments", [home_path])
expect(attachments.ok).to_equal(true)
expect(attachments.content.contains("diagram.png")).to_equal(true)

val attachment_target = "/tmp/simple_editor_attachment_target.md"
expect(rt_file_write_text(attachment_target, "# Attachment Target\n")).to_equal(true)
val inserted_attachment = editor_mcp_dispatch(session, "editor.wiki_attachment_insert", [attachment_target, "assets/photo.png", "Photo"])
expect(inserted_attachment.ok).to_equal(true)
expect(rt_file_read_text(attachment_target)).to_equal("# Attachment Target\n![Photo](assets/photo.png)\n")

val stored_root = "/tmp/simple_editor_mcp_attachment_store"
expect(rt_dir_create_all(stored_root + "/incoming")).to_equal(true)
rt_file_delete(stored_root + "/assets/image.png")
rt_file_delete(stored_root + "/assets/image-1.png")
val stored_target = stored_root + "/Note.md"
val stored_source = stored_root + "/incoming/image.png"
expect(rt_file_write_text(stored_target, "# Stored Attachment\n")).to_equal(true)
expect(rt_file_write_text(stored_source, "image-bytes")).to_equal(true)
val stored_attachment = editor_mcp_dispatch(session, "editor.wiki_attachment_insert", [stored_target, stored_source, "Image", "assets"])
expect(stored_attachment.ok).to_equal(true)
expect(stored_attachment.content.contains("assets/image")).to_equal(true)
expect(rt_file_read_text(stored_target).contains("# Stored Attachment\n![Image](assets/image")).to_equal(true)
expect(rt_file_write_text(stored_source, "image-bytes-new")).to_equal(true)
val renamed_attachment = editor_mcp_dispatch(session, "editor.wiki_attachment_insert", [stored_target, stored_source, "Image 2", "assets"])
expect(renamed_attachment.ok).to_equal(true)
expect(renamed_attachment.content.contains("assets/image-")).to_equal(true)
expect(rt_file_read_text(stored_target).contains("![Image 2](assets/image-")).to_equal(true)

val callouts = editor_mcp_dispatch(session, "editor.wiki_callouts", [home_path])
expect(callouts.ok).to_equal(true)
expect(callouts.content.contains("warning")).to_equal(true)

val graph = editor_mcp_dispatch(session, "editor.wiki_graph_edges", [home_path])
expect(graph.ok).to_equal(true)
expect(graph.content.contains("embed")).to_equal(true)

val tpl_result = editor_mcp_dispatch(session, "editor.wiki_template_preview", ["# {{title}}\n{{date}}\n", "Note", "2026-05-13"])
expect(tpl_result.ok).to_equal(true)
expect(tpl_result.content.contains("# Note")).to_equal(true)
val tpl_custom = editor_mcp_dispatch(session, "editor.wiki_template_preview", ["# {{title}}\nOwner: {{owner}}\nStatus: {{status}}\n", "Note", "2026-05-13", "owner=Docs", "status", "Active"])
expect(tpl_custom.ok).to_equal(true)
expect(tpl_custom.content).to_equal("# Note\nOwner: Docs\nStatus: Active\n")

val template_root = "/tmp/simple_editor_templates"
expect(rt_dir_create_all(template_root)).to_equal(true)
val tpl_path = template_root + "/meeting.md"
val target_path = "/tmp/simple_editor_template_target.md"
expect(rt_file_write_text(tpl_path, "## {{title}}\nDate: {{date}}\n")).to_equal(true)
expect(rt_file_write_text(target_path, "# Target\n")).to_equal(true)
val templates = editor_mcp_dispatch(session, "editor.wiki_template_list", [template_root])
expect(templates.ok).to_equal(true)
expect(templates.content.contains(tpl_path)).to_equal(true)
val inserted_template = editor_mcp_dispatch(session, "editor.wiki_template_insert", [tpl_path, target_path, "Planning", "2026-05-15"])
expect(inserted_template.ok).to_equal(true)
expect(rt_file_read_text(target_path)).to_equal("# Target\n## Planning\nDate: 2026-05-15\n")
val custom_tpl_path = template_root + "/project.md"
val custom_target_path = "/tmp/simple_editor_template_custom_target.md"
expect(rt_file_write_text(custom_tpl_path, "## {{title}}\nOwner: {{owner}}\nStatus: {{status}}\n")).to_equal(true)
expect(rt_file_write_text(custom_target_path, "# Custom Target\n")).to_equal(true)
val inserted_custom_template = editor_mcp_dispatch(session, "editor.wiki_template_insert", [custom_tpl_path, custom_target_path, "Project", "2026-05-15", "owner=Docs", "status", "Active"])
expect(inserted_custom_template.ok).to_equal(true)
expect(rt_file_read_text(custom_target_path)).to_equal("# Custom Target\n## Project\nOwner: Docs\nStatus: Active\n")

val daily = editor_mcp_dispatch(session, "editor.wiki_daily_note", ["2026-05-13", "Daily", "# {{title}}\n"])
expect(daily.ok).to_equal(true)
expect(daily.content.contains("Daily/2026-05-13.md")).to_equal(true)
val configured_daily = editor_mcp_dispatch(session, "editor.wiki_daily_note", ["2026-05-13", "Journal/2026", "# {{title}}\nDate: {{date}}\n", "{{date}}-daily", "markdown"])
expect(configured_daily.ok).to_equal(true)
expect(configured_daily.content.contains("Journal/2026/2026-05-13-daily.markdown")).to_equal(true)
expect(configured_daily.content.contains("# 2026-05-13-daily")).to_equal(true)

val daily_root = "/tmp/simple_editor_daily"
expect(rt_dir_create_all(daily_root)).to_equal(true)
val created_daily = editor_mcp_dispatch(session, "editor.wiki_daily_note_create", ["2026-05-14", daily_root, "# {{title}}\nCreated: {{date}}\n"])
expect(created_daily.ok).to_equal(true)
expect(created_daily.content.contains(daily_root + "/2026-05-14.md")).to_equal(true)
expect(rt_file_read_text(daily_root + "/2026-05-14.md")).to_equal("# 2026-05-14\nCreated: 2026-05-14\n")
val configured_daily_root = "/tmp/simple_editor_daily_configured"
expect(rt_dir_create_all(configured_daily_root + "/2026")).to_equal(true)
val created_configured_daily = editor_mcp_dispatch(session, "editor.wiki_daily_note_create", ["2026-05-14", configured_daily_root + "/2026", "# {{title}}\nCreated: {{date}}\n", "{{date}}-daily", "markdown"])
expect(created_configured_daily.ok).to_equal(true)
expect(created_configured_daily.content.contains(configured_daily_root + "/2026/2026-05-14-daily.markdown")).to_equal(true)
expect(rt_file_read_text(configured_daily_root + "/2026/2026-05-14-daily.markdown")).to_equal("# 2026-05-14-daily\nCreated: 2026-05-14\n")
```

</details>

#### indexes a markdown vault root through editor MCP tools

1. var session = EditSession new
   - Expected: quick.ok is true
   - Expected: quick.content contains `alpha_path`
   - Expected: quick.content does not contain `ignored_path`
   - Expected: search.ok is true
   - Expected: search.content contains `alpha_path`
   - Expected: search.content contains `Finish vault index`
   - Expected: search.content contains `score=`
   - Expected: search.content does not contain `ignored_path`
   - Expected: rt_file_read_text(root + "/.simple-vault-search.cache") contains `SIMPLE_MD_SEARCH_INDEX`
   - Expected: rt_file_write_text(alpha_path, "---\ntags: project\n---\n# Alpha\nFresh cache phrase\n- [ ] Finish vault index #project\n") is true
   - Expected: refreshed_search.ok is true
   - Expected: refreshed_search.content contains `Fresh cache phrase`
   - Expected: rt_file_read_text(root + "/.simple-vault-search.cache") contains `Fresh cache phrase`
   - Expected: backlinks.ok is true
   - Expected: backlinks.content contains `home_path`
   - Expected: unresolved.ok is true
   - Expected: unresolved.content contains `Missing`
   - Expected: tags.ok is true
   - Expected: tags.content contains `alpha_path`
   - Expected: props.ok is true
   - Expected: props.content contains `tags: project`
   - Expected: tasks.ok is true
   - Expected: tasks.content contains `Finish vault index`
   - Expected: graph.ok is true
   - Expected: graph.content contains `link`
   - Expected: graph.content contains `embed`
   - Expected: embeds.ok is true
   - Expected: embeds.content contains `Alpha`
   - Expected: callouts.ok is true
   - Expected: callouts.content contains `tip`
   - Expected: attachments.ok is true
   - Expected: attachments.content contains `diagram.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_editor_wiki_vault"
expect(rt_dir_create_all(root + "/Projects")).to_equal(true)
expect(rt_dir_create_all(root + "/Archive")).to_equal(true)
val home_path = root + "/Home.md"
val alpha_path = root + "/Projects/Alpha.md"
val ignored_path = root + "/Archive/ignored.txt"
expect(rt_file_write_text(home_path, "# Home\nSee [[Alpha]] and [[Missing]].\n![[Alpha|embedded]]\n![[diagram.png]]\n> [!TIP] Vault callout\n")).to_equal(true)
expect(rt_file_write_text(alpha_path, "---\ntags: project\n---\n# Alpha\n- [ ] Finish vault index #project\n")).to_equal(true)
expect(rt_file_write_text(ignored_path, "[[Home]]")).to_equal(true)
var session = EditSession.new()

val quick = editor_mcp_dispatch(session, "editor.wiki_vault_quick_switch", [root, "alpha"])
expect(quick.ok).to_equal(true)
expect(quick.content.contains(alpha_path)).to_equal(true)
expect(quick.content.contains(ignored_path)).to_equal(false)

val search = editor_mcp_dispatch(session, "editor.wiki_vault_search", [root, "vault index"])
expect(search.ok).to_equal(true)
expect(search.content.contains(alpha_path)).to_equal(true)
expect(search.content.contains("Finish vault index")).to_equal(true)
expect(search.content.contains("score=")).to_equal(true)
expect(search.content.contains(ignored_path)).to_equal(false)
expect(rt_file_read_text(root + "/.simple-vault-search.cache").contains("SIMPLE_MD_SEARCH_INDEX")).to_equal(true)

expect(rt_file_write_text(alpha_path, "---\ntags: project\n---\n# Alpha\nFresh cache phrase\n- [ ] Finish vault index #project\n")).to_equal(true)
val refreshed_search = editor_mcp_dispatch(session, "editor.wiki_vault_search", [root, "fresh cache"])
expect(refreshed_search.ok).to_equal(true)
expect(refreshed_search.content.contains("Fresh cache phrase")).to_equal(true)
expect(rt_file_read_text(root + "/.simple-vault-search.cache").contains("Fresh cache phrase")).to_equal(true)

val backlinks = editor_mcp_dispatch(session, "editor.wiki_vault_backlinks", [root, alpha_path])
expect(backlinks.ok).to_equal(true)
expect(backlinks.content.contains(home_path)).to_equal(true)

val unresolved = editor_mcp_dispatch(session, "editor.wiki_vault_unresolved", [root])
expect(unresolved.ok).to_equal(true)
expect(unresolved.content.contains("Missing")).to_equal(true)

val tags = editor_mcp_dispatch(session, "editor.wiki_vault_tags", [root, "project"])
expect(tags.ok).to_equal(true)
expect(tags.content.contains(alpha_path)).to_equal(true)

val props = editor_mcp_dispatch(session, "editor.wiki_vault_properties", [root, alpha_path])
expect(props.ok).to_equal(true)
expect(props.content.contains("tags: project")).to_equal(true)

val tasks = editor_mcp_dispatch(session, "editor.wiki_vault_tasks", [root, "open"])
expect(tasks.ok).to_equal(true)
expect(tasks.content.contains("Finish vault index")).to_equal(true)

val graph = editor_mcp_dispatch(session, "editor.wiki_vault_graph_edges", [root, ""])
expect(graph.ok).to_equal(true)
expect(graph.content.contains("link")).to_equal(true)
expect(graph.content.contains("embed")).to_equal(true)

val embeds = editor_mcp_dispatch(session, "editor.wiki_vault_embeds", [root, home_path])
expect(embeds.ok).to_equal(true)
expect(embeds.content.contains("Alpha")).to_equal(true)

val callouts = editor_mcp_dispatch(session, "editor.wiki_vault_callouts", [root, home_path])
expect(callouts.ok).to_equal(true)
expect(callouts.content.contains("tip")).to_equal(true)

val attachments = editor_mcp_dispatch(session, "editor.wiki_vault_attachments", [root, home_path])
expect(attachments.ok).to_equal(true)
expect(attachments.content.contains("diagram.png")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_md_wiki_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor markdown wiki index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
