# mail_html_render_spec

> Mail HTML render spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mail_html_render_spec

Mail HTML render spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/mail_html_render_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Mail HTML render spec.

Verifies the Mail surface HTML renderer — the "render mail like Gmail" slice of
the office suite. `render_message_html` renders a single email (sender, subject,
date, body; unread subject bold) and `render_mailbox_html` renders the mailbox
as a folder sidebar plus a message list over `MailApp.new()` demo data.

All assertions are over the produced HTML string, so they run on the test
runner without the f64/i32 toolchain fragility.

## Scenarios

### mail HTML render: single message

#### renders the sender and subject

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_message_html(_msg("Quarterly draft is ready", "Please review.", false))
expect(html).to_start_with("<article class=\"mail-message\"")
expect(html).to_contain("Alex Rivera")
expect(html).to_contain("alex@example.com")
expect(html).to_contain("Quarterly draft is ready")
expect(html).to_contain("Please review.")
expect(html).to_contain("2026-03-24")
```

</details>

#### renders an unread subject in bold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_message_html(_msg("Unread mail", "body", false))
expect(html).to_contain("font-weight: 700;")
```

</details>

#### renders a read subject in normal weight

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_message_html(_msg("Read mail", "body", true))
expect(html).to_contain("font-weight: 400;")
```

</details>

#### HTML-escapes a <script> in the subject

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_message_html(_msg("<script>alert(1)</script>", "body", false))
expect(html).to_contain("&lt;script&gt;alert(1)&lt;/script&gt;")
expect(html.contains("<script>")).to_be(false)
```

</details>

### mail HTML render: mailbox list

#### wraps the mailbox in a styled container

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_mailbox_html(MailApp.new())
expect(html).to_start_with("<div class=\"mailbox\"")
```

</details>

#### lists all demo emails

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_mailbox_html(MailApp.new())
expect(html).to_contain("Quarterly draft is ready")
expect(html).to_contain("Updated staffing sheet")
expect(html).to_contain("Slides for product review")
expect(html).to_contain("Follow-up draft")
expect(html).to_contain("Old vendor thread")
```

</details>

#### shows the folder sidebar

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_mailbox_html(MailApp.new())
expect(html).to_contain("class=\"mail-sidebar\"")
expect(html).to_contain("Inbox")
expect(html).to_contain("Sent")
expect(html).to_contain("Drafts")
expect(html).to_contain("Trash")
```

</details>

#### shows the unread count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_mailbox_html(MailApp.new())
expect(html).to_contain("2 unread")
```

</details>

#### escapes email content in the list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = MailApp.new()
app.emails = [_msg("<b>x</b>", "body", false)]
val html = render_mailbox_html(app)
expect(html).to_contain("&lt;b&gt;x&lt;/b&gt;")
expect(html.contains("<b>x</b>")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
