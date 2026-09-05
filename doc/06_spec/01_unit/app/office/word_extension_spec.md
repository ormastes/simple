# Word Extension Specification

> Tests covering writer extension manifest, WordApp writer.* command dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Word Extension Specification

## Scenarios

### writer extension manifest

#### declares the simple.rich_document custom editor and namespaced writer.* commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = writer_ext_manifest()
expect(m.contributes_custom_editors.len()).to_equal(1)
expect(m.contributes_custom_editors[0].document_kind).to_equal("simple.rich_document")
expect(m.contributes_commands.len()).to_equal(12)
expect(m.contributes_commands[0].id).to_equal("writer.format_bold")
expect(m.contributes_commands[11].id).to_equal("writer.save")
```

</details>

### WordApp writer.* command dispatch

#### dispatches writer.format_bold through the registry and mutates a real RichDocument

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = WordApp.open("draft.txt", "Hello world")
expect(app.modified).to_equal(false)
app.handle_event(UIEvent.Action(name: "format_bold"))
expect(app.modified).to_equal(true)
val bi = app.editor.cursor.block_index
val block = app.editor.doc.blocks[bi]
var saw_bold = false
for s in block.spans:
    match s.style:
        case Bold:
            saw_bold = true
        case _:
            pass_do_nothing("non-bold span")
expect(saw_bold).to_equal(true)
```

</details>

#### dispatches writer.format_h1 and changes the block kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = WordApp.open("draft.txt", "Hello world")
app.handle_event(UIEvent.Action(name: "format_h1"))
val bi = app.editor.cursor.block_index
val block = app.editor.doc.blocks[bi]
var is_heading1 = false
match block.kind:
    case Heading1:
        is_heading1 = true
    case _:
        pass_do_nothing("not a heading")
expect(is_heading1).to_equal(true)
```

</details>

#### writer.save serializes the document through the codec and clears modified

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = WordApp.open("draft.txt", "Hello world")
app.handle_event(UIEvent.Action(name: "format_bold"))
expect(app.modified).to_equal(true)
app.handle_event(UIEvent.Action(name: "save"))
expect(app.modified).to_equal(false)
val saved = app.save()
expect(saved.contains("title:")).to_equal(true)
expect(saved.contains("Hello world")).to_equal(true)
```

</details>

#### an unrecognized action does not register as a writer.* command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = WordApp.new()
app.handle_event(UIEvent.Action(name: "not_a_real_action"))
expect(app.modified).to_equal(false)
```

</details>

#### an unknown writer command id returns Err, not a crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = WordApp.new()
val result = app.commands.run("writer.does_not_exist", "0")
match result:
    case Ok(_):
        expect("unknown command").to_equal("should have failed")
    case Err(msg):
        expect(msg.contains("no handler")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_extension_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering writer extension manifest, WordApp writer.* command dispatch.
- writer extension manifest
- WordApp writer.* command dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
