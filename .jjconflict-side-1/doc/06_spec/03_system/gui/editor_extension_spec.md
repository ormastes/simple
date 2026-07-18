# Editor Extension Specification

> <details>

<!-- sdn-diagram:id=editor_extension_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_extension_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_extension_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_extension_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Extension Specification

## Scenarios

### editor extension — manifest

#### defines ExtensionManifest struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/manifest.spl")
expect(src.contains("struct ExtensionManifest:")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
expect(src.contains("version: text")).to_equal(true)
expect(src.contains("main: text")).to_equal(true)
expect(src.contains("activation_events: [text]")).to_equal(true)
```

</details>

#### defines ExtensionCommand and ExtensionLanguage

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/manifest.spl")
expect(src.contains("struct ExtensionCommand:")).to_equal(true)
expect(src.contains("struct ExtensionLanguage:")).to_equal(true)
expect(src.contains("struct ExtensionDebugAdapterManifest:")).to_equal(true)
expect(src.contains("struct ExtensionKeybinding:")).to_equal(true)
```

</details>

#### has extension_manifest_parse function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/manifest.spl")
expect(src.contains("fn extension_manifest_load(path: text) -> ExtensionManifest")).to_equal(true)
```

</details>

#### parses name, version, main from manifest fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/manifest.spl")
expect(src.contains("_extension_manifest_text_value(content, \"name\")")).to_equal(true)
expect(src.contains("_extension_manifest_text_value(content, \"version\")")).to_equal(true)
expect(src.contains("_extension_manifest_text_value(content, \"main\")")).to_equal(true)
```

</details>

#### parses debug adapter contributions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/manifest.spl")
expect(src.contains("contributes_debug_adapters: [ExtensionDebugAdapterManifest]")).to_equal(true)
expect(src.contains("_extension_manifest_debug_adapter_list(content)")).to_equal(true)
expect(src.contains("ExtensionDebugAdapterManifest")).to_equal(true)
```

</details>

### editor extension — host

#### defines ExtensionHost class

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("class ExtensionHost:")).to_equal(true)
expect(src.contains("extensions: [ExtensionEntry]")).to_equal(true)
expect(src.contains("command_registry: [ExtensionCommandEntry]")).to_equal(true)
expect(src.contains("debug_adapter_registry: [ExtensionDebugAdapterEntry]")).to_equal(true)
expect(src.contains("context_registry: [ExtensionContextEntry]")).to_equal(true)
expect(src.contains("event_log: [ExtensionEventRecord]")).to_equal(true)
expect(src.contains("invocation_queue: [ExtensionCommandInvocation]")).to_equal(true)
expect(src.contains("runtime_policy: ExtensionRuntimePolicy")).to_equal(true)
expect(src.contains("runtime_dispatch_log: [ExtensionRuntimeDispatchRecord]")).to_equal(true)
```

</details>

#### has index_extension for two-phase loading

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("me index_extension(path: text)")).to_equal(true)
```

</details>

#### discovers external extension manifests without executing them

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("extern fn rt_dir_walk(path: text) -> [text]")).to_equal(true)
expect(src.contains("me discover_extensions(roots: [text]) -> i64")).to_equal(true)
expect(src.contains("_extension_host_is_manifest_path(file)")).to_equal(true)
expect(src.contains("_extension_host_dirname(file)")).to_equal(true)
expect(src.contains("me.index_extension(extension_dir)")).to_equal(true)
```

</details>

#### can register in-memory built-in manifests

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("me register_manifest(manifest: ExtensionManifest, path: text)")).to_equal(true)
expect(src.contains("me._unregister_contributions(manifest.name)")).to_equal(true)
expect(src.contains("fn extension_host_with_builtins() -> ExtensionHost")).to_equal(true)
expect(src.contains("register_manifest(spl_language_manifest(), \"<builtin>\")")).to_equal(true)
expect(src.contains("register_manifest(md_language_manifest(), \"<builtin>\")")).to_equal(true)
```

</details>

#### has activate and deactivate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("me activate(name: text) -> bool")).to_equal(true)
expect(src.contains("me deactivate(name: text) -> bool")).to_equal(true)
```

</details>

#### routes VS Code style activation events

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("me activate_event(event: text) -> i64")).to_equal(true)
expect(src.contains("activation_event == event or activation_event == \"*\"")).to_equal(true)
expect(src.contains("me activate_language(language_id: text) -> i64")).to_equal(true)
expect(src.contains("\"onLanguage:\" + language_id")).to_equal(true)
expect(src.contains("me activate_command(command_id: text) -> i64")).to_equal(true)
expect(src.contains("\"onCommand:\" + command_id")).to_equal(true)
```

</details>

#### registers contributions on activate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("me._register_contributions(entry.manifest)")).to_equal(true)
expect(src.contains("me._register_context(entry.manifest, entry.path)")).to_equal(true)
```

</details>

#### unregisters contributions on deactivate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("me._unregister_contributions(entry.manifest.name)")).to_equal(true)
expect(src.contains("me._unregister_context(entry.manifest.name)")).to_equal(true)
```

</details>

#### tracks extension API contexts for active extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("struct ExtensionContextEntry:")).to_equal(true)
expect(src.contains("struct ExtensionEventRecord:")).to_equal(true)
expect(src.contains("fn find_context(name: text) -> ExtensionContext")).to_equal(true)
expect(src.contains("me _register_context(manifest: ExtensionManifest, path: text)")).to_equal(true)
expect(src.contains("extension_context_new(path, manifest.name)")).to_equal(true)
```

</details>

#### emits editor events through extension subscriptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("me emit_event(event: text, payload: text) -> i64")).to_equal(true)
expect(src.contains("extension_context_is_subscribed(entry.context, event)")).to_equal(true)
expect(src.contains("ExtensionEventRecord(")).to_equal(true)
expect(src.contains("me subscribe(extension_name: text, event: text) -> bool")).to_equal(true)
expect(src.contains("fn event_count() -> i64")).to_equal(true)
```

</details>

#### provides find_command and find_language_for_ext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("fn find_command(command_id: text) -> ExtensionCommandEntry")).to_equal(true)
expect(src.contains("fn command_registered(command_id: text) -> bool")).to_equal(true)
expect(src.contains("fn find_language_for_ext(file_ext: text) -> text")).to_equal(true)
```

</details>

#### provides debug adapter registry lookups

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("struct ExtensionDebugAdapterEntry:")).to_equal(true)
expect(src.contains("fn find_debug_adapter(adapter_id: text) -> ExtensionDebugAdapterEntry")).to_equal(true)
expect(src.contains("fn debug_adapter_registered(adapter_id: text) -> bool")).to_equal(true)
expect(src.contains("manifest.contributes_debug_adapters")).to_equal(true)
```

</details>

#### queues external command invocations for runtime execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("struct ExtensionCommandInvocation:")).to_equal(true)
expect(src.contains("me dispatch_external_command(command_id: text, payload: text) -> ExtensionCommandInvocation")).to_equal(true)
expect(src.contains("status: \"pending-runtime\"")).to_equal(true)
expect(src.contains("me.invocation_queue.push(invocation)")).to_equal(true)
expect(src.contains("fn pending_invocation_count() -> i64")).to_equal(true)
expect(src.contains("fn last_invocation() -> ExtensionCommandInvocation")).to_equal(true)
```

</details>

#### gates runtime execution behind explicit policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("struct ExtensionRuntimePolicy:")).to_equal(true)
expect(src.contains("struct ExtensionRuntimeDispatchRecord:")).to_equal(true)
expect(src.contains("fn extension_runtime_policy_default() -> ExtensionRuntimePolicy")).to_equal(true)
expect(src.contains("enabled: false")).to_equal(true)
expect(src.contains("me set_runtime_policy(policy: ExtensionRuntimePolicy)")).to_equal(true)
expect(src.contains("me drain_invocation_queue() -> i64")).to_equal(true)
expect(src.contains("fn _dispatch_runtime_invocation(invocation: ExtensionCommandInvocation) -> ExtensionRuntimeDispatchRecord")).to_equal(true)
expect(src.contains("reason: \"runtime disabled\"")).to_equal(true)
expect(src.contains("reason: \"extension root not allowed\"")).to_equal(true)
expect(src.contains("status: \"ready-sandbox\"")).to_equal(true)
expect(src.contains("status: \"ready-external-process\"")).to_equal(true)
```

</details>

#### has named runtime policy constructors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("fn extension_runtime_policy_sandboxed(allowed_roots: [text]) -> ExtensionRuntimePolicy")).to_equal(true)
expect(src.contains("fn extension_runtime_policy_external_process(allowed_roots: [text]) -> ExtensionRuntimePolicy")).to_equal(true)
expect(src.contains("allow_external_process: false")).to_equal(true)
expect(src.contains("allow_external_process: true")).to_equal(true)
```

</details>

### editor extension — API

#### defines ExtensionContext struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/api.spl")
expect(src.contains("struct ExtensionContext:")).to_equal(true)
expect(src.contains("storage_path: text")).to_equal(true)
expect(src.contains("workspace_state_keys: [text]")).to_equal(true)
expect(src.contains("subscriptions: [text]")).to_equal(true)
expect(src.contains("workspace_state_values: [text]")).to_equal(true)
expect(src.contains("struct ExtensionCapability:")).to_equal(true)
```

</details>

#### has register_command and subscribe helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/api.spl")
expect(src.contains("fn extension_context_new")).to_equal(true)
expect(src.contains("fn extension_context_subscribe")).to_equal(true)
expect(src.contains("fn extension_context_is_subscribed")).to_equal(true)
```

</details>

#### has workspace state helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/api.spl")
expect(src.contains("fn extension_context_set_state")).to_equal(true)
expect(src.contains("fn extension_context_get_state")).to_equal(true)
expect(src.contains("workspace_state_values: values")).to_equal(true)
val host = read_text("src/lib/editor/extensions/host.spl")
expect(host.contains("me set_workspace_state(extension_name: text, key: text, value: text) -> bool")).to_equal(true)
expect(host.contains("fn get_workspace_state(extension_name: text, key: text) -> text")).to_equal(true)
```

</details>

### editor extension — built-in Simple language

#### defines spl_language_manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("fn spl_language_manifest() -> ExtensionManifest")).to_equal(true)
expect(src.contains("\"simple-language\"")).to_equal(true)
expect(src.contains(".spl")).to_equal(true)
expect(src.contains("ExtensionDebugAdapterManifest(")).to_equal(true)
expect(src.contains("id: \"simple\"")).to_equal(true)
expect(src.contains("program: \"bin/simple\"")).to_equal(true)
```

</details>

### editor extension — built-in Markdown language

#### defines md_language_manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_manifest() -> ExtensionManifest")).to_equal(true)
expect(src.contains("\"markdown-language\"")).to_equal(true)
expect(src.contains(".md")).to_equal(true)
expect(src.contains("\"md.preview\"")).to_equal(true)
expect(src.contains("\"md.toggleBold\"")).to_equal(true)
expect(src.contains("\"md.toggleItalic\"")).to_equal(true)
```

</details>

#### activates Markdown contributions through the extension host

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = extension_host_with_builtins()
expect(host.command_registered("md.toggleBold")).to_equal(false)
expect(host.find_language_for_ext(".md")).to_equal("")
val activated = host.activate_language("markdown")
expect(activated).to_equal(1)
expect(host.command_registered("md.toggleBold")).to_equal(true)
expect(host.command_registered("md.toggleItalic")).to_equal(true)
expect(host.find_language_for_ext(".md")).to_equal("markdown")
expect(host.find_language_for_ext(".markdown")).to_equal("markdown")
```

</details>

#### dispatches Markdown command contract results with state and payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val outline_result = md_commands_dispatch("markdown.toggleOutline", state, "# Root\n\n## Child\n", 0, 0)
expect(md_editor_state_outline_visible(md_command_result_state(outline_result))).to_equal(true)
expect(outline_result.status_message).to_equal("Outline shown")
val table_result = md_commands_dispatch("markdown.insertTable", md_command_result_state(outline_result), "", 0, 0)
expect(table_result.insert_text.contains("| Header 1 | Header 2 | Header 3 |")).to_equal(true)
expect(table_result.status_message).to_equal("")
val stats_result = md_commands_dispatch("markdown.documentStats", md_command_result_state(table_result), "one two\nthree", 0, 0)
expect(stats_result.status_message.contains("Lines: 2")).to_equal(true)
expect(stats_result.status_message.contains("Words: ~3")).to_equal(true)
```

</details>

#### queues wiki plugin commands only after activation and runtime policy checks

1. ExtensionCommand
2. host register manifest
   - Expected: host.command_registered("wiki.backlinks") is false
   - Expected: invocation.status equals `pending-runtime`
   - Expected: invocation.command_id equals `wiki.backlinks`
   - Expected: invocation.payload equals `/workspace/notes/Home.md`
   - Expected: host.command_registered("wiki.backlinks") is true
   - Expected: host.pending_invocation_count() equals `1`
   - Expected: host.drain_invocation_queue() equals `1`
   - Expected: blocked.status equals `blocked-runtime`
   - Expected: blocked.reason equals `runtime disabled`
3. host set runtime policy
   - Expected: invocation2.status equals `pending-runtime`
   - Expected: host.drain_invocation_queue() equals `1`
   - Expected: ready.status equals `ready-sandbox`
   - Expected: ready.command_id equals `wiki.backlinks`
   - Expected: ready.main equals `/workspace/extensions/wiki-contract-test/main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = ExtensionManifest(
    name: "wiki-contract-test",
    version: "1.0.0",
    main: "main.spl",
    activation_events: ["onCommand:wiki.backlinks"],
    contributes_commands: [
        ExtensionCommand(id: "wiki.backlinks", title: "Wiki Backlinks")
    ],
    contributes_languages: [],
    contributes_debug_adapters: [],
    contributes_themes: [],
    contributes_keybindings: []
)
val host = ExtensionHost.new()
host.register_manifest(manifest, "/workspace/extensions/wiki-contract-test")
expect(host.command_registered("wiki.backlinks")).to_equal(false)
val invocation = host.dispatch_external_command("wiki.backlinks", "/workspace/notes/Home.md")
expect(invocation.status).to_equal("pending-runtime")
expect(invocation.command_id).to_equal("wiki.backlinks")
expect(invocation.payload).to_equal("/workspace/notes/Home.md")
expect(host.command_registered("wiki.backlinks")).to_equal(true)
expect(host.pending_invocation_count()).to_equal(1)
expect(host.drain_invocation_queue()).to_equal(1)
val blocked = host.last_runtime_dispatch()
expect(blocked.status).to_equal("blocked-runtime")
expect(blocked.reason).to_equal("runtime disabled")
host.set_runtime_policy(extension_runtime_policy_sandboxed(["/workspace/extensions"]))
val invocation2 = host.dispatch_external_command("wiki.backlinks", "/workspace/notes/Other.md")
expect(invocation2.status).to_equal("pending-runtime")
expect(host.drain_invocation_queue()).to_equal(1)
val ready = host.last_runtime_dispatch()
expect(ready.status).to_equal("ready-sandbox")
expect(ready.command_id).to_equal("wiki.backlinks")
expect(ready.main).to_equal("/workspace/extensions/wiki-contract-test/main.spl")
```

</details>

### editor extension — host contribution wiring

#### has extension_contribute_highlighting function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("fn extension_contribute_highlighting(host: ExtensionHost, language_id: text, line: text) -> text")).to_equal(true)
expect(src.contains("line")).to_equal(true)
expect(src.contains("fn extension_contribute_highlighting")).to_equal(true)
```

</details>

#### has extension_contribute_completions function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("fn extension_contribute_completions(host: ExtensionHost, language_id: text, prefix: text) -> [text]")).to_equal(true)
expect(src.contains("extension_simple_keyword_completions(prefix)")).to_equal(true)
```

</details>

#### has Simple keyword completions in extension host

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src.contains("fn extension_simple_keyword_completions(prefix: text) -> [text]")).to_equal(true)
expect(src.contains("keyword.starts_with(prefix)")).to_equal(true)
```

</details>

#### has md_block_kinds in md_language

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_manifest() -> ExtensionManifest")).to_equal(true)
expect(src.contains("markdown")).to_equal(true)
expect(src.contains(".markdown")).to_equal(true)
expect(src.contains("md.toggleBold")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_extension_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor extension — manifest
- editor extension — host
- editor extension — API
- editor extension — built-in Simple language
- editor extension — built-in Markdown language
- editor extension — host contribution wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
