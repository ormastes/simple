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
| Updated | 2026-08-26 |
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

- renders the sender and subject


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders the sender and subject")
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

- renders an unread subject in bold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an unread subject in bold")
val html = render_message_html(_msg("Unread mail", "body", false))
expect(html).to_contain("font-weight: 700;")
```

</details>

#### renders a read subject in normal weight

- renders a read subject in normal weight


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a read subject in normal weight")
val html = render_message_html(_msg("Read mail", "body", true))
expect(html).to_contain("font-weight: 400;")
```

</details>

#### HTML-escapes a <script> in the subject

- HTML-escapes a <script> in the subject


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HTML-escapes a <script> in the subject")
val html = render_message_html(_msg("<script>alert(1)</script>", "body", false))
expect(html).to_contain("&lt;script&gt;alert(1)&lt;/script&gt;")
expect(html.contains("<script>")).to_be(false)
```

</details>

### mail HTML render: mailbox list

#### wraps the mailbox in a styled container

- wraps the mailbox in a styled container


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps the mailbox in a styled container")
val html = render_mailbox_html(MailApp.new())
expect(html).to_start_with("<div class=\"mailbox\"")
```

</details>

#### lists all demo emails

- lists all demo emails


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all demo emails")
val html = render_mailbox_html(MailApp.new())
expect(html).to_contain("Quarterly draft is ready")
expect(html).to_contain("Updated staffing sheet")
expect(html).to_contain("Slides for product review")
expect(html).to_contain("Follow-up draft")
expect(html).to_contain("Old vendor thread")
```

</details>

#### shows the folder sidebar

- shows the folder sidebar


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows the folder sidebar")
val html = render_mailbox_html(MailApp.new())
expect(html).to_contain("class=\"mail-sidebar\"")
expect(html).to_contain("Inbox")
expect(html).to_contain("Sent")
expect(html).to_contain("Drafts")
expect(html).to_contain("Trash")
```

</details>

#### shows the unread count

- shows the unread count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows the unread count")
val html = render_mailbox_html(MailApp.new())
expect(html).to_contain("2 unread")
```

</details>

#### escapes email content in the list

- escapes email content in the list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes email content in the list")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `df2a218d3fc1f87eaca0de6c1bf9ec9a384422a3a6941372ce1c387137c4d93e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df2a218d3fc1f87eaca0de6c1bf9ec9a384422a3a6941372ce1c387137c4d93e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df2a218d3fc1f87eaca0de6c1bf9ec9a384422a3a6941372ce1c387137c4d93e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/mail_html_render_spec.spl
mirror: doc/06_spec/01_unit/app/office/mail_html_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/mail_html_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/mail_html_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/mail_html_render_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the sender and subject' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/mail_html_render_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders an unread subject in bold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/mail_html_render_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a read subject in normal weight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
