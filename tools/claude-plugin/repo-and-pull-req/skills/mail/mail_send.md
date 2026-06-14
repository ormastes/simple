# Mail Send Skill

Compose and send emails, reply, or forward via `bin/mail` CLI.

## Prerequisites

- Email account configured (`bin/mail auth status`)

## Procedure

### Send New Email

```bash
bin/mail send \
  --to "recipient@example.com" \
  --subject "Subject line" \
  --body "Message body text"
```

With CC/BCC:
```bash
bin/mail send \
  --to "to@example.com" \
  --cc "cc@example.com" \
  --bcc "bcc@example.com" \
  --subject "Subject" \
  --body "Body"
```

From file:
```bash
bin/mail send --to "to@example.com" --subject "Report" --input report.txt
```

### Reply to Message

```bash
# Get the UID from inbox first
bin/mail inbox --limit 10

# Reply
bin/mail reply <uid> --body "Thanks for the update!"
```

Reply auto-sets:
- `Re: ` prefix on subject
- `In-Reply-To` and `References` headers for threading
- Quoted original message

### Forward Message

```bash
bin/mail forward <uid> --to "forward-to@example.com" --body "FYI"
```

### Using Specific Account

```bash
bin/mail send --account work --to "..." --subject "..." --body "..."
```

## Integration

- Use with `/mail notify` to send PR event notifications
- Can be called from review_loop agent to notify about PR status changes
