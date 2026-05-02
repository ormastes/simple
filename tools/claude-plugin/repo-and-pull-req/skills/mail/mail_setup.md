# Mail Setup Skill

Setup email accounts via `bin/mail` CLI (Gmail, Outlook, Yahoo, ProtonMail, Fastmail, or any IMAP/SMTP).

## Prerequisites

- `bin/mail version` — CLI available
- `curl` with IMAP/SMTP support: `curl --version | grep imap`

## Procedure

### Step 1 — Verify CLI

```bash
bin/mail version
```

### Step 2 — Add Email Account

Ask user to run interactively: `! bin/mail auth login --provider gmail`

Provider-specific notes:

**Gmail:**
- Requires App Password (not regular password)
- 2-Step Verification must be enabled
- Create at: https://myaccount.google.com/apppasswords

**Outlook / Office 365:**
- Use regular password or App Password
- IMAP: outlook.office365.com:993, SMTP: smtp.office365.com:587

**Yahoo:**
- Requires App Password
- Create at: https://login.yahoo.com/account/security

**ProtonMail:**
- Requires ProtonMail Bridge running locally
- Bridge provides local IMAP (127.0.0.1:1143) and SMTP (127.0.0.1:1025)
- Use Bridge password, not account password

**Fastmail:**
- Supports App Password
- Create at: Fastmail Settings → Privacy & Security → App Passwords

### Step 3 — Verify

```bash
bin/mail auth status            # Check connection
bin/mail inbox --limit 3        # List recent messages
bin/mail folder list            # List folders
```

## Multi-Account Setup

Add additional accounts with `--account NAME`:
```bash
! bin/mail auth login --account work --provider gmail
! bin/mail auth login --account personal --provider outlook
```

Set default: `bin/mail config set default_account work`

## Verification Checklist

- [ ] `bin/mail version` succeeds
- [ ] `bin/mail auth status` shows connected account
- [ ] `bin/mail inbox` lists messages
- [ ] `~/.config/mail-cli/config.json` exists (mode 600)
