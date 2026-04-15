# Plan: repo-and-pull-req Plugin — Full Status (2026-04-11)

## Overall Scope

Unified Claude Code plugin with 3 CLI tools, 15 skills, 2 agents, and 3 dispatcher skills for GitHub, Jira, bug tracking, and email integration.

---

## COMPLETED (All Code Written + Validated)

### CLI Tool 1: `bin/jira` (Jira + Confluence CLI, mirrors `gh`)
- **Path:** `tools/jira-cli/` (7 files)
- **Commands:** auth, issue, project, sprint, wiki, api, me, config, version, help
- **Config:** `~/.config/jira-cli/config.json`
- **Files:**
  - `tools/jira-cli/bin/jira` — main dispatcher
  - `tools/jira-cli/lib/config.shs` — config management
  - `tools/jira-cli/lib/api.shs` — raw REST API client (`jira api <endpoint>`)
  - `tools/jira-cli/lib/auth.shs` — login/logout/status/token
  - `tools/jira-cli/lib/issue.shs` — create/list/view/edit/comment/move/close/reopen/delete
  - `tools/jira-cli/lib/project.shs` — list/view
  - `tools/jira-cli/lib/sprint.shs` — list/current
  - `tools/jira-cli/lib/wiki.shs` — Confluence create/list/view/edit/search/space
  - `bin/jira` → symlink

### CLI Tool 2: `bin/bug` (Unified Bug Tracker)
- **Path:** `tools/bug-cli/` (7 files)
- **Commands:** list, view, search, triage, fix, config, version, help
- **Sources:** GitHub Issues (via `gh`) + Jira Issues (via `bin/jira`)
- **Config:** `~/.config/bug-cli/config.json`
- **Files:**
  - `tools/bug-cli/bin/bug` — main dispatcher
  - `tools/bug-cli/lib/config.shs` — config + severity keywords
  - `tools/bug-cli/lib/github.shs` — wraps `gh issue list/view`
  - `tools/bug-cli/lib/jira.shs` — wraps `bin/jira issue list/view`
  - `tools/bug-cli/lib/aggregate.shs` — merges/deduplicates from both sources
  - `tools/bug-cli/lib/triage.shs` — keyword-based severity/component classification
  - `tools/bug-cli/lib/format.shs` — table/detail/JSON output
  - `bin/bug` → symlink

### CLI Tool 3: `bin/mail` (Gmail-like Email Client)
- **Path:** `tools/mail-cli/` (10 files)
- **Commands:** auth, inbox, read, send, reply, forward, search, folder, star, archive, delete, move, draft, config
- **Providers:** Gmail, Outlook/365, Yahoo, ProtonMail (Bridge), Fastmail, any IMAP/SMTP
- **Protocol:** IMAP/SMTP via curl (native protocol support verified — curl 8.7.1)
- **Config:** `~/.config/mail-cli/config.json` (multi-account)
- **Files:**
  - `tools/mail-cli/bin/mail` — main dispatcher
  - `tools/mail-cli/lib/config.shs` — multi-account config + provider presets
  - `tools/mail-cli/lib/imap.shs` — IMAP ops via curl
  - `tools/mail-cli/lib/smtp.shs` — SMTP send via curl (TLS + STARTTLS)
  - `tools/mail-cli/lib/auth.shs` — login with provider presets, connection test
  - `tools/mail-cli/lib/inbox.shs` — inbox list, read, search
  - `tools/mail-cli/lib/send.shs` — send, reply (threading), forward
  - `tools/mail-cli/lib/folder.shs` — folder list/create, star, archive, delete, move
  - `tools/mail-cli/lib/draft.shs` — draft list/create/send
  - `tools/mail-cli/lib/format.shs` — RFC 2822 compose, header parse, MIME decode
  - `bin/mail` → symlink

### Claude Plugin: `repo-and-pull-req`
- **Path:** `tools/claude-plugin/repo-and-pull-req/`
- **plugin.json:** 15 skills + 2 agents — validated via `build.sh`
- **Marketplace:** Entry added to `tools/claude-plugin/marketplace/.claude-plugin/marketplace.json`

#### Skills (15 total):
| Category | Skill | File | Description |
|----------|-------|------|-------------|
| git | gh_setup | `skills/git/gh_setup.md` | Install/auth gh CLI |
| git | gh_push | `skills/git/gh_push.md` | Create PR via temp jj bookmark |
| git | gh_wiki | `skills/git/gh_wiki.md` | Auto-generate GitHub wiki pages |
| git | gh_pull_req_review | `skills/git/gh_pull_req_review.md` | Single-pass PR review |
| jira | jira_setup | `skills/jira/jira_setup.md` | Custom jira-cli setup |
| jira | jira_push | `skills/jira/jira_push.md` | Create/update Jira issues |
| jira | jira_wiki | `skills/jira/jira_wiki.md` | Create/update Confluence pages |
| jira | jira_pull_req_review | `skills/jira/jira_pull_req_review.md` | Jira-linked PR review |
| bug | bug_setup | `skills/bug/bug_setup.md` | Setup bug tracking |
| bug | bug_review | `skills/bug/bug_review.md` | AI-powered bug triage |
| bug | bug_fix | `skills/bug/bug_fix.md` | Analyze + propose code fix |
| mail | mail_setup | `skills/mail/mail_setup.md` | Setup email accounts |
| mail | mail_send | `skills/mail/mail_send.md` | Compose/send/reply |
| mail | mail_review | `skills/mail/mail_review.md` | Review PR notification emails |
| mail | mail_notify | `skills/mail/mail_notify.md` | Send PR event notifications |

#### Agents (2):
| Agent | File | Schedule | Description |
|-------|------|----------|-------------|
| review_loop | `agents/review_loop.md` | Every 1h | Autonomous PR review |
| bug_triage | `agents/bug_triage.md` | Every 4h | Autonomous bug classification |

#### Dispatcher Skills (3):
| Skill | File | Commands |
|-------|------|----------|
| `/repo_and_pull_req` | `.claude/skills/repo_and_pull_req.md` | setup, push, wiki, review |
| `/bug_review` | `.claude/skills/bug_review.md` | setup, list, view, triage, fix |
| `/mail` | `.claude/skills/mail.md` | setup, inbox, read, send, reply, search, review, notify |

---

## PENDING — Requires User Interaction

### 1. Jira Account Setup
- Create account: https://www.atlassian.com/software/jira/free (ormastes@gmail.com)
- Get API token: https://id.atlassian.com/manage-profile/security/api-tokens
- Run: `! bin/jira auth login`
- Verify: `bin/jira auth status`, `bin/jira me`
- Enable in bug-cli: `bin/bug config set jira_enabled true`

### 2. Email Account Setup
- Enable 2-Step Verification: https://myaccount.google.com/security
- Create App Password: https://myaccount.google.com/apppasswords
- Run: `! bin/mail auth login --provider gmail`
- Verify: `bin/mail auth status`, `bin/mail inbox --limit 5`

### 3. End-to-End Testing (after auth)
- `bin/bug list` — verify aggregation
- `bin/mail inbox` — verify email
- `/repo_and_pull_req push` — create PR with plugin code
- `/repo_and_pull_req wiki` — create knowledge pages
- `/repo_and_pull_req review loop <pr#>` — start review loop

---

## FUTURE ENHANCEMENTS

- OAuth 2.0 for mail-cli (Gmail, Microsoft)
- HTML email rendering (strip tags)
- Attachment support (MIME multipart)
- Thread view (group by References/In-Reply-To)
- JMAP protocol (Fastmail)
- POP3 support
- Bug auto-fix via `/sstack` pipeline

## Technical Notes

- Bash: `#!/usr/bin/env bash` → homebrew bash 5.3.9 (macOS `/bin/bash` is 3.2)
- curl 8.7.1: native `imap`, `imaps`, `smtp`, `smtps` support
- Config files: `chmod 600` for credential security
- Third-party `ankitpokhrel/jira-cli`: installed then uninstalled — only custom `bin/jira` remains
