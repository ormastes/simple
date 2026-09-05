# Claude Full AttachmentMessage Skill Discovery

## Scope

This manual mirrors the focused executable SSpec for production
`AttachmentMessage.spl` skill-discovery dispatch.

| Field | Value |
|---|---|
| Requirement | `REQ-LLM-CARET-HIDDEN-008` |
| Evidence class | Supporting parts-bin render-model metadata |
| Production owner | `src/app/llm_caret/claude_full/components/messages/AttachmentMessage.spl` |
| Executable spec | `test/03_system/tools/llm/claude_full/components/messages/AttachmentMessage_spec.spl` |
| Tests | 3 |
| Active tests | 3 |
| Execution in this tranche | 0 scenarios executed; no PASS is claimed |

The source remains an otherwise unreachable parts bin in this tranche. These
scenarios prove only exact `AttachmentRender` values returned by the production
dispatcher. They do not claim shipped CLI/TUI reachability, hosted UI behavior,
widget integration, visual layout, or pixel output.

## Fixture and helper contract

`setup_attachment_skill_discovery_fixture` constructs one `skill_discovery`
attachment with three skills in this order:

1. `search [sk-1]`
2. `deploy`
3. `review [sk-3]`

`check_attachment_skill_discovery_render` requires:

| Field | Expected value |
|---|---|
| `visible` | `true` |
| `kind` | `skill_discovery` |
| `label` | `3 relevant skills` |
| `detail` | Ordered fixture text, with only the scenario-authorized feedback suffix |
| `count` | `3` |
| `color` | Empty |
| `children` | Empty |

`check_hidden_attachment_render` requires the fully empty hidden shape:
`visible = false`, `kind = hidden`, empty `label`, `detail`, `color`, and
`children`, with `count = 0`.

## Scenario 1: Ordered plural discovery

The dispatcher receives the enabled non-demo fixture. It preserves input
order, formats the plural label and short IDs, and appends feedback for the
first skill only.

<details>
<summary>Executable SSpec</summary>

```spl
it "should render ordered plural skill discovery through AttachmentMessage":
    step("Load the skill-discovery attachment fixture")
    val attachment = setup_attachment_skill_discovery_fixture()
    step("Render skill discovery through AttachmentMessage")
    val render = attachmentMessageRender(attachment, false, false, false, false, true, false)
    step("Check skill-discovery content and redaction")
    expect(check_attachment_skill_discovery_render(render, "search [sk-1], deploy, review [sk-3] /skill-feedback sk-1")).to_equal("complete")
```

</details>

## Scenario 2: Demo feedback suppression

Demo mode removes the first-skill feedback suffix while preserving the same
ordered skill names and short-ID formatting. Unrelated dispatcher flags do not
change the skill-discovery branch.

<details>
<summary>Executable SSpec</summary>

```spl
it "should suppress first-skill feedback in demo without changing ordered content":
    step("Load the skill-discovery attachment fixture")
    val attachment = setup_attachment_skill_discovery_fixture()
    step("Render skill discovery through AttachmentMessage")
    val render = attachmentMessageRender(attachment, true, true, true, true, true, true)
    step("Check skill-discovery content and redaction")
    expect(check_attachment_skill_discovery_render(render, "search [sk-1], deploy, review [sk-3]")).to_equal("complete")
```

</details>

## Scenario 3: Fail-closed hidden states

Disabled skill search, an empty skill list, and an unsupported attachment type
carrying skill-shaped data all return the complete hidden shape. The
unsupported type avoids suppressing legitimate non-skill attachment kinds
while proving that private skill metadata does not leak.

<details>
<summary>Executable SSpec</summary>

```spl
it "should hide disabled empty and wrong-type skill discovery without leaking content":
    step("Load the skill-discovery attachment fixture")
    val disabledAttachment = setup_attachment_skill_discovery_fixture()
    val emptyAttachment = AttachmentModel.empty("skill_discovery")
    val wrongTypeAttachment = AttachmentModel.empty("unsupported_skill_discovery")
    wrongTypeAttachment.skills = [AttachmentSkill.new("private-skill", "secret-short-id")]
    step("Render skill discovery through AttachmentMessage")
    val disabledRender = attachmentMessageRender(disabledAttachment, false, false, false, false, false, false)
    val emptyRender = attachmentMessageRender(emptyAttachment, false, false, false, false, true, false)
    val wrongTypeRender = attachmentMessageRender(wrongTypeAttachment, false, false, false, false, true, false)
    step("Check skill-discovery content and redaction")
    expect(check_hidden_attachment_render(disabledRender)).to_equal("complete")
    expect(check_hidden_attachment_render(emptyRender)).to_equal("complete")
    expect(check_hidden_attachment_render(wrongTypeRender)).to_equal("complete")
```

</details>

## Execution note

This manual was synchronized directly from the authored executable scenario
bodies. Runtime execution and doc generation were intentionally out of scope
for this bounded tranche, so no runtime result or PASS status is asserted.
