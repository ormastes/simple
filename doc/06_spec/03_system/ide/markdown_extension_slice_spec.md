# IDE Extension Kernel — Markdown Vertical Slice (L1)

> End-to-end proof that the markdown builtin is a real extension riding the kernel instead of a pile of direct imports: the `markdown-language` manifest declares `markdown.toggle_bold` with an `onCommand:` activation event, the extension starts INACTIVE on a fresh host, the first `host.dispatch_command("markdown.toggle_bold", ...)` lazily activates it and runs the typed handler against a real `EditorBuffer`'s text (wrapping the selection in `**`), a second dispatch removes the wrap (toggle), and the markdown diagnostics provider resolves through the same CommandRegistry and returns real diagnostics for a fixture markdown text.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IDE Extension Kernel — Markdown Vertical Slice (L1)

End-to-end proof that the markdown builtin is a real extension riding the kernel instead of a pile of direct imports: the `markdown-language` manifest declares `markdown.toggle_bold` with an `onCommand:` activation event, the extension starts INACTIVE on a fresh host, the first `host.dispatch_command("markdown.toggle_bold", ...)` lazily activates it and runs the typed handler against a real `EditorBuffer`'s text (wrapping the selection in `**`), a second dispatch removes the wrap (toggle), and the markdown diagnostics provider resolves through the same CommandRegistry and returns real diagnostics for a fixture markdown text.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | IDE-EXT-KERNEL L1 |
| Category | Infrastructure |
| Status | In Progress |
| Requirements | doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (L1) |
| Source | `test/03_system/ide/markdown_extension_slice_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end proof that the markdown builtin is a real extension riding the
kernel instead of a pile of direct imports: the `markdown-language` manifest
declares `markdown.toggle_bold` with an `onCommand:` activation event, the
extension starts INACTIVE on a fresh host, the first
`host.dispatch_command("markdown.toggle_bold", ...)` lazily activates it and
runs the typed handler against a real `EditorBuffer`'s text (wrapping the
selection in `**`), a second dispatch removes the wrap (toggle), and the
markdown diagnostics provider resolves through the same CommandRegistry and
returns real diagnostics for a fixture markdown text.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `md_language_manifest` | Typed manifest declaring `markdown.toggle_bold` + `onCommand:` activation |
| `md_toggle_bold_handler` | Typed `fn(text) -> Result<text, text>` command handler |
| `md_language_diagnose_handler` | Diagnostics provider registered through the CommandRegistry |
| `ExtensionHost.dispatch_command` | Lazy activation + real handler execution |

## Related Specifications

- [extension_kernel_walking_skeleton_spec.spl](extension_kernel_walking_skeleton_spec.spl)
- [lifecycle_spec.spl](../../01_unit/lib/editor/extensions/lifecycle_spec.spl)

## Scenarios

### IDE extension kernel L1: markdown vertical slice

#### manifest declares markdown.toggle_bold with an onCommand activation event

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- manifest declares markdown.toggle_bold with an onCommand activation event
   - Expected: m.name equals `MD_EXTENSION_NAME`
   - Expected: m.schema_version equals `simple.ide.extension/1`
   - Expected: has_command is true
   - Expected: has_event is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("manifest declares markdown.toggle_bold with an onCommand activation event")
val m = md_language_manifest()
expect(m.name).to_equal(MD_EXTENSION_NAME)
expect(m.schema_version).to_equal("simple.ide.extension/1")
var has_command = false
for cmd in m.contributes_commands:
    if cmd.id == TOGGLE_BOLD_COMMAND:
        has_command = true
expect(has_command).to_equal(true)
var has_event = false
for evt in m.activation_events:
    if evt == "onCommand:" + TOGGLE_BOLD_COMMAND:
        has_event = true
expect(has_event).to_equal(true)
```

</details>

#### starts inactive, toggles bold on via lazy dispatch, then off again on a real buffer

- starts inactive, toggles bold on via lazy dispatch, then off again on a real buffer
   - Expected: host.is_active(MD_EXTENSION_NAME) is false
   - Expected: host.command_handler_registered(TOGGLE_BOLD_COMMAND) is true
   - Expected: line equals `hello world`
   - Expected: host.is_active(MD_EXTENSION_NAME) is true
   - Expected: buffer.to_text() equals `# Title\n\nhello **world**`
   - Expected: buffer.to_text() equals `# Title\n\nhello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts inactive, toggles bold on via lazy dispatch, then off again on a real buffer")
val host = build_markdown_host()
expect(host.is_active(MD_EXTENSION_NAME)).to_equal(false)
expect(host.command_handler_registered(TOGGLE_BOLD_COMMAND)).to_equal(true)

var buffer = build_markdown_buffer()
val row = 2
val line = buffer.line_at(row)
expect(line).to_equal("hello world")

# selection over "world" (cols 6..11)
val first = host.dispatch_command(TOGGLE_BOLD_COMMAND, toggle_payload(6, 6, 11, line))
Then_dispatch_ok(first, "hello **world**")
expect(host.is_active(MD_EXTENSION_NAME)).to_equal(true)
if val Ok(bolded) = first:
    replace_buffer_line(buffer, row, bolded)
expect(buffer.to_text()).to_equal("# Title\n\nhello **world**")

# dispatch again over "world" (now cols 8..13) — toggle removes the wrap
val second = host.dispatch_command(TOGGLE_BOLD_COMMAND,
    toggle_payload(8, 8, 13, buffer.line_at(row)))
Then_dispatch_ok(second, "hello world")
if val Ok(unbolded) = second:
    replace_buffer_line(buffer, row, unbolded)
expect(buffer.to_text()).to_equal("# Title\n\nhello world")
```

</details>

#### toggles bold around the word at the cursor when there is no selection

- toggles bold around the word at the cursor when there is no selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("toggles bold around the word at the cursor when there is no selection")
val host = build_markdown_host()
val result = host.dispatch_command(TOGGLE_BOLD_COMMAND, toggle_payload(7, -1, -1, "hello world"))
Then_dispatch_ok(result, "hello **world**")
```

</details>

#### toggles a task checkbox through the kernel route (Integration Wave I)

- toggles a task checkbox through the kernel route (Integration Wave I)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("toggles a task checkbox through the kernel route (Integration Wave I)")
val host = build_markdown_host()
val first = host.dispatch_command("markdown.toggle_task", "- [ ] write spec")
Then_dispatch_ok(first, "- [x] write spec")
val second = host.dispatch_command("markdown.toggle_task", "- [x] write spec")
Then_dispatch_ok(second, "- [ ] write spec")
# non-task lines pass through unchanged — shells report "not a task"
val third = host.dispatch_command("markdown.toggle_task", "plain text")
Then_dispatch_ok(third, "plain text")
```

</details>

#### diagnostics provider resolves through the registry and returns real diagnostics

- diagnostics provider resolves through the registry and returns real diagnostics
   - Expected: host.is_active(MD_EXTENSION_NAME) is true
   - Expected: encoded contains `Heading requires a space after '#'`
   - Expected: encoded contains `Empty link target`
   - Expected: encoded.starts_with("0|1|warning|") is true
   - Expected: "diagnostics dispatch" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostics provider resolves through the registry and returns real diagnostics")
val host = build_markdown_host()
# activate through the kernel's lazy onCommand path first
host.activate_command(TOGGLE_BOLD_COMMAND)
expect(host.is_active(MD_EXTENSION_NAME)).to_equal(true)
val result = host.dispatch_command(DIAGNOSTICS_COMMAND, FIXTURE_MD_TEXT)
match result:
    case Ok(encoded):
        expect(encoded.contains("Heading requires a space after '#'")).to_equal(true)
        expect(encoded.contains("Empty link target")).to_equal(true)
        # first diagnostic row encodes line|col|severity|message
        expect(encoded.starts_with("0|1|warning|")).to_equal(true)
    case Err(_):
        expect("diagnostics dispatch").to_equal("should have succeeded")
```

</details>

#### diagnostics dispatch on an inactive extension fails cleanly, not by crashing

- diagnostics dispatch on an inactive extension fails cleanly, not by crashing
   - Expected: "dispatch" equals `should have failed while inactive`
   - Expected: message contains `not active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostics dispatch on an inactive extension fails cleanly, not by crashing")
val host = build_markdown_host()
val result = host.dispatch_command(DIAGNOSTICS_COMMAND, FIXTURE_MD_TEXT)
match result:
    case Ok(_):
        expect("dispatch").to_equal("should have failed while inactive")
    case Err(message):
        expect(message.contains("not active")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (L1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-IDE-EXT-KERNEL-L1`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `486603dd4ba3fdcb46a71f123ff0092b9540952e406ccd9bb1c58abfd57d8e67`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `486603dd4ba3fdcb46a71f123ff0092b9540952e406ccd9bb1c58abfd57d8e67`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `486603dd4ba3fdcb46a71f123ff0092b9540952e406ccd9bb1c58abfd57d8e67`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/ide/markdown_extension_slice_spec.spl
mirror: doc/06_spec/03_system/ide/markdown_extension_slice_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/ide/markdown_extension_slice_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/ide/markdown_extension_slice_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/ide/markdown_extension_slice_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/ide/markdown_extension_slice_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'manifest declares markdown.toggle_bold with an onCommand activation event' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ide/markdown_extension_slice_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts inactive, toggles bold on via lazy dispatch, then off again on a real buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ide/markdown_extension_slice_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'toggles bold around the word at the cursor when there is no selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
