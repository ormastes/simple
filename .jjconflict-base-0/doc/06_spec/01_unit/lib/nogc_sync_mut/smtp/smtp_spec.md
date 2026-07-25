# Smtp Specification

> <details>

<!-- sdn-diagram:id=smtp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smtp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smtp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smtp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 62 | 62 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smtp Specification

## Scenarios

### SMTP command serialization — exact RFC 5321 wire bytes

#### HELO command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_helo("mail.example.com")).to_equal("HELO mail.example.com\r\n")
```

</details>

#### EHLO command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_ehlo("client.example.com")).to_equal("EHLO client.example.com\r\n")
```

</details>

#### MAIL FROM command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_mail_from("sender@example.com")).to_equal("MAIL FROM:<sender@example.com>\r\n")
```

</details>

#### RCPT TO command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_rcpt_to("rcpt@example.com")).to_equal("RCPT TO:<rcpt@example.com>\r\n")
```

</details>

#### DATA command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_data()).to_equal("DATA\r\n")
```

</details>

#### QUIT command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_quit()).to_equal("QUIT\r\n")
```

</details>

#### RSET command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_rset()).to_equal("RSET\r\n")
```

</details>

#### NOOP command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_noop()).to_equal("NOOP\r\n")
```

</details>

#### STARTTLS command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_starttls()).to_equal("STARTTLS\r\n")
```

</details>

#### AUTH PLAIN command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_auth_plain()).to_equal("AUTH PLAIN\r\n")
```

</details>

#### AUTH LOGIN command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_command_auth_login()).to_equal("AUTH LOGIN\r\n")
```

</details>

#### DATA terminator is CRLF.CRLF

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(message_terminate()).to_equal("\r\n.\r\n")
```

</details>

### SMTP reply-code parsing

#### parse code from single-line 220 response

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_parse_code("220 mail.example.com ESMTP ready\r\n")).to_equal(220)
```

</details>

#### parse code from 250 response

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_parse_code("250 OK\r\n")).to_equal(250)
```

</details>

#### parse code from 500 error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_parse_code("500 Syntax error\r\n")).to_equal(500)
```

</details>

#### parse message from 250 OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_parse_message("250 OK\r\n")).to_equal("OK\r\n")
```

</details>

#### parse message from 220 banner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = response_parse_message("220 mail.example.com ESMTP\r\n")
expect(msg.starts_with("mail.example.com")).to_equal(true)
```

</details>

#### single-line response is NOT multiline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_is_multiline("250 OK\r\n")).to_equal(false)
```

</details>

#### multiline response detected by dash at position 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_is_multiline("250-STARTTLS\r\n")).to_equal(true)
```

</details>

#### multiline continuation line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_is_multiline("250-SIZE 14680064\r\n")).to_equal(true)
```

</details>

#### last line of multiline is not multiline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(response_is_multiline("250 AUTH PLAIN LOGIN\r\n")).to_equal(false)
```

</details>

### SMTP reply-code classification

#### 220 is success code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_is_success_code(220)).to_equal(true)
```

</details>

#### 250 is success code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_is_success_code(250)).to_equal(true)
```

</details>

#### 354 is not a 2xx success code (it is a 3xx positive intermediate)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_is_success_code(354)).to_equal(false)
```

</details>

#### 421 is error code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_is_error_code(421)).to_equal(true)
```

</details>

#### 500 is error code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_is_error_code(500)).to_equal(true)
```

</details>

#### 550 is error code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_is_error_code(550)).to_equal(true)
```

</details>

#### 220 is not error code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_is_error_code(220)).to_equal(false)
```

</details>

#### code description 250

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = smtp_code_description(250)
expect(d.starts_with("Requested")).to_equal(true)
```

</details>

#### code description 354 mentions CRLF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = smtp_code_description(354)
expect(d.starts_with("Start")).to_equal(true)
```

</details>

### SMTP session state machine

#### initial state is INITIAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = smtp_session_new()
expect(s).to_equal("INITIAL")
```

</details>

#### after HELO state is HELO

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_session_after_helo()).to_equal("HELO")
```

</details>

#### after MAIL state is MAIL

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_session_after_mail()).to_equal("MAIL")
```

</details>

#### after RCPT state is RCPT

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_session_after_rcpt()).to_equal("RCPT")
```

</details>

#### can_mail only in HELO state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_can_mail("HELO")).to_equal(true)
expect(smtp_can_mail("INITIAL")).to_equal(false)
expect(smtp_can_mail("MAIL")).to_equal(false)
```

</details>

#### can_rcpt in MAIL state

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_can_rcpt("MAIL")).to_equal(true)
```

</details>

#### can_rcpt in RCPT state (multiple recipients)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_can_rcpt("RCPT")).to_equal(true)
```

</details>

#### can_rcpt not in HELO state

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_can_rcpt("HELO")).to_equal(false)
```

</details>

#### can_data only in RCPT state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_can_data("RCPT")).to_equal(true)
expect(smtp_can_data("MAIL")).to_equal(false)
```

</details>

### SMTP dot-stuffing (RFC 5321 §4.5.2)

#### body without dots is unchanged before terminator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "Hello world\r\n"
val stuffed = smtp_dot_stuff(body)
expect(stuffed.starts_with("Hello world\r\n")).to_equal(true)
expect(stuffed.ends_with("\r\n.\r\n")).to_equal(true)
```

</details>

#### line beginning with dot gets extra dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "line one\r\n.line with dot\r\nline three\r\n"
val stuffed = smtp_dot_stuff(body)
expect(stuffed.index_of("\r\n..line with dot\r\n") != -1).to_equal(true)
```

</details>

#### dot-only line becomes double-dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "before\r\n.\r\nafter\r\n"
val stuffed = smtp_dot_stuff(body)
expect(stuffed.index_of("\r\n..\r\n") != -1).to_equal(true)
```

</details>

#### terminator CRLF.CRLF appended

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stuffed = smtp_dot_stuff("hello\r\n")
expect(stuffed.ends_with("\r\n.\r\n")).to_equal(true)
```

</details>

#### undot reverses dot-stuffing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello\r\n.dotline\r\nend\r\n"
val stuffed = smtp_dot_stuff(original)
val restored = smtp_undot_stuff(stuffed)
expect(restored).to_equal(original)
```

</details>

#### undot strips terminator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stuffed = "Hello\r\n.\r\n"
val restored = smtp_undot_stuff(stuffed)
expect(restored.ends_with("\r\n.\r\n")).to_equal(false)
```

</details>

#### undot on body with doubled-dot restores single

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "normal\r\n..doubly-dotted\r\n"
val restored = smtp_undot_stuff(body)
expect(restored.index_of("\r\n.doubly-dotted\r\n") != -1).to_equal(true)
```

</details>

#### round-trip multi-line body with mixed dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "line1\r\n.sec\r\n..dbl\r\nnormal\r\n"
val stuffed = smtp_dot_stuff(original)
val restored = smtp_undot_stuff(stuffed)
expect(restored).to_equal(original)
```

</details>

### SMTP email address validation

#### valid address passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(email_validate("user@example.com")).to_equal(true)
```

</details>

#### address without @ fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(email_validate("userexample.com")).to_equal(false)
```

</details>

#### address without domain dot fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(email_validate("user@localhost")).to_equal(false)
```

</details>

#### empty string fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(email_validate("")).to_equal(false)
```

</details>

#### multiple @ fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(email_validate("a@b@c.com")).to_equal(false)
```

</details>

#### subject injection stripped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = smtp_sanitize_smtp_subject("Hello\r\nBcc: evil@x.com")
expect(s.index_of("\r\n") == -1).to_equal(true)
```

</details>

### SMTP AUTH encoding

#### AUTH LOGIN username base64 — user encodes to dXNlcg==

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(auth_login_encode_username("user")).to_equal("dXNlcg==")
```

</details>

#### AUTH LOGIN password base64 — pass encodes to cGFzcw==

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(auth_login_encode_password("pass")).to_equal("cGFzcw==")
```

</details>

#### AUTH PLAIN base64 — NUL+user+NUL+pass encodes to AHVzZXIAcGFzcw==

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(auth_plain_encode("user", "pass")).to_equal("AHVzZXIAcGFzcw==")
```

</details>

### SMTP secure (SMTPS) port constants

#### SMTPS implicit TLS port is 465

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtps_default_port()).to_equal(465)
```

</details>

#### STARTTLS submission port is 587

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_starttls_port()).to_equal(587)
```

</details>

#### SMTP cleartext port is 25

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smtp_cleartext_port()).to_equal(25)
```

</details>

### SMTP message headers

#### From header format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(header_from("alice@example.com")).to_equal("From: alice@example.com\r\n")
```

</details>

#### To header format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(header_to("bob@example.com")).to_equal("To: bob@example.com\r\n")
```

</details>

#### Subject header format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(header_subject("Hello World")).to_equal("Subject: Hello World\r\n")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/smtp/smtp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMTP command serialization — exact RFC 5321 wire bytes
- SMTP reply-code parsing
- SMTP reply-code classification
- SMTP session state machine
- SMTP dot-stuffing (RFC 5321 §4.5.2)
- SMTP email address validation
- SMTP AUTH encoding
- SMTP secure (SMTPS) port constants
- SMTP message headers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 62 |
| Active scenarios | 62 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
