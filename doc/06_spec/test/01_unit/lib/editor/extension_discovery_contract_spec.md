# Extension Discovery Contract Specification

> <details>

<!-- sdn-diagram:id=extension_discovery_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=extension_discovery_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

extension_discovery_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=extension_discovery_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extension Discovery Contract Specification

## Scenarios

### editor extension discovery contract

#### walks configured roots and indexes extension manifests

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = read_text("src/lib/editor/extensions/host.spl")
expect(host.contains("me discover_extensions(roots: [text]) -> i64")).to_equal(true)
expect(host.contains("rt_dir_walk(root)")).to_equal(true)
expect(host.contains("_extension_host_is_manifest_path(file)")).to_equal(true)
expect(host.contains("_extension_host_dirname(file)")).to_equal(true)
expect(host.contains("me.index_extension(extension_dir)")).to_equal(true)
```

</details>

#### discovers and activates a real manifest from an extension root

1. var host = ExtensionHost new
   - Expected: host.discover_extensions([root]) equals `1`
   - Expected: host.extension_count() equals `1`
   - Expected: host.is_active("demo-extension") is false
   - Expected: host.command_registered("demo.hello") is false
   - Expected: host.activate_command("demo.hello") equals `1`
   - Expected: host.is_active("demo-extension") is true
   - Expected: host.command_registered("demo.hello") is true
   - Expected: extension_command_entry_name(entry) equals `demo-extension`
   - Expected: extension_command_entry_command_id(entry) equals `demo.hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = extension_discovery_tmp_root()
val manifest = "{\n" +
    "  \"name\": \"demo-extension\",\n" +
    "  \"version\": \"1.0.0\",\n" +
    "  \"main\": \"main.spl\",\n" +
    "  \"activation_events\": [\"onCommand:demo.hello\"],\n" +
    "  \"contributes_commands\": [{\"id\": \"demo.hello\", \"title\": \"Demo Hello\"}]\n" +
    "}\n"
expect(rt_file_write_text(root + "/demo/extension.sdn", manifest)).to_equal(true)

var host = ExtensionHost.new()
expect(host.discover_extensions([root])).to_equal(1)
expect(host.extension_count()).to_equal(1)
expect(host.is_active("demo-extension")).to_equal(false)
expect(host.command_registered("demo.hello")).to_equal(false)

expect(host.activate_command("demo.hello")).to_equal(1)
expect(host.is_active("demo-extension")).to_equal(true)
expect(host.command_registered("demo.hello")).to_equal(true)
val entry = host.find_command("demo.hello")
expect(extension_command_entry_name(entry)).to_equal("demo-extension")
expect(extension_command_entry_command_id(entry)).to_equal("demo.hello")
```

</details>

#### discovers the embedded IDE example extension manifest

1. var host = ExtensionHost new
   - Expected: host.discover_extensions(["examples/10_tooling/ide/extensions"]) equals `1`
   - Expected: host.extension_count() equals `1`
   - Expected: host.activate_language("markdown") equals `1`
   - Expected: host.command_registered("markdown.notes.preview") is true
   - Expected: extension_command_entry_name(entry) equals `markdown-notes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = ExtensionHost.new()
expect(host.discover_extensions(["examples/10_tooling/ide/extensions"])).to_equal(1)
expect(host.extension_count()).to_equal(1)
expect(host.activate_language("markdown")).to_equal(1)
expect(host.command_registered("markdown.notes.preview")).to_equal(true)
val entry = host.find_command("markdown.notes.preview")
expect(extension_command_entry_name(entry)).to_equal("markdown-notes")
```

</details>

#### resolves the embedded IDE extension runtime entrypoint behind sandbox policy

1. var host = ExtensionHost new
   - Expected: host.discover_extensions(["examples/10_tooling/ide/extensions"]) equals `1`
2. host set runtime policy
   - Expected: invocation.status equals `pending-runtime`
   - Expected: host.drain_invocation_queue() equals `1`
   - Expected: record.extension_name equals `markdown-notes`
   - Expected: record.main equals `examples/10_tooling/ide/extensions/markdown-notes/main.spl`
   - Expected: record.status equals `ready-sandbox`
   - Expected: record.reason equals `sandbox runner required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = ExtensionHost.new()
expect(host.discover_extensions(["examples/10_tooling/ide/extensions"])).to_equal(1)
host.set_runtime_policy(extension_runtime_policy_sandboxed(["examples/10_tooling/ide/extensions"]))
val invocation = host.dispatch_external_command("markdown.notes.preview", "")
expect(invocation.status).to_equal("pending-runtime")
expect(host.drain_invocation_queue()).to_equal(1)
val record = host.last_runtime_dispatch()
expect(record.extension_name).to_equal("markdown-notes")
expect(record.main).to_equal("examples/10_tooling/ide/extensions/markdown-notes/main.spl")
expect(record.status).to_equal("ready-sandbox")
expect(record.reason).to_equal("sandbox runner required")
```

</details>

#### keeps built-in extension modules in the canonical extension tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = read_text("src/lib/editor/extensions/builtin/graph_language.spl")
expect(graph.contains("fn graph_language_manifest() -> ExtensionManifest")).to_equal(true)
expect(graph.contains("sdn-graph-language")).to_equal(true)
```

</details>

#### loads extension roots during editor controller startup

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = read_text("src/app/editor/editor_controller.spl")
val app_roots = read_text("src/app/editor/editor_extension_roots.spl")
val lib_roots = read_text("src/lib/editor/extensions/roots.spl")
expect(controller.contains("host.discover_extensions(editor_extension_roots())")).to_equal(true)
expect(app_roots.contains("SIMPLE_EDITOR_EXTENSION_PATH")).to_equal(true)
expect(app_roots.contains("rt_env_get(\"HOME\")")).to_equal(true)
expect(app_roots.contains("editor_extension_roots_from_inputs(configured, home)")).to_equal(true)
expect(lib_roots.contains(".simple/editor/extensions")).to_equal(true)
expect(lib_roots.contains(".vscode/simple-editor/extensions")).to_equal(true)
expect(lib_roots.contains("/usr/local/share/simple/editor/extensions")).to_equal(true)
expect(lib_roots.contains("/usr/share/simple/editor/extensions")).to_equal(true)
expect(lib_roots.contains("rt_env_get")).to_equal(false)
expect(lib_roots.contains("rt_file_exists")).to_equal(false)
expect(lib_roots.contains("rt_dir_walk")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/extension_discovery_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor extension discovery contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
