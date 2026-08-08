# devhub `email` — Gmail-semantics facade over mail-cli (IMAP/SMTP) and Outlook (Graph)

Read-only survey basis: `tools/mail-cli/` (bash/curl IMAP+SMTP CLI) and
`src/app/itf/{cmd_outlook,adapter_outlook,adapter_outlook_curl}.spl` (MS Graph
adapter), plus Gmail IMAP-extension and Graph API knowledge (no local Gmail
CLI tools installed at research time — `himalaya/gmailctl/notmuch/mutt/aerc/
gam` all absent, no network calls made).

---

## 1. What exists today

| Capability | mail-cli (IMAP/SMTP, `tools/mail-cli/`) | Outlook adapter (Graph, `src/app/itf/`) |
|---|---|---|
| Auth model | Basic (password / app-password / `password_cmd`), per-provider preset incl. `outlook` IMAP/SMTP | **App-only OAuth2 client-credentials** (`oauth2_client_credentials_token`), single **shared mailbox** via `/users/{upn}/...` — NOT a per-user delegated login. No device-code/auth-code flow exists anywhere in `std.*.oauth2`. |
| Multi-account | Yes, `~/.config/mail-cli/config.json`, `--account NAME` | One mailbox per `~/.config/itf/auth.sdn` `[outlook]` section |
| list/inbox | `cmd_inbox` (ALL/UNSEEN, threads, table/json) | `outlook messages <FOLDER_ID>` (`$filter`, `$top`) |
| read | `cmd_read` (marks `\Seen`) | `outlook get <MSG_ID>` (`$expand=attachments`) |
| search | `cmd_search --from/--subject/--since/--before` → IMAP `SEARCH` | **None.** Only `--filter` (raw Graph `$filter` string) on `messages`; `$search` explicitly unsupported (adapter comment: Graph rejects `$filter`+`$search` together, so this adapter prefers `$filter` and ignores `$search`) |
| send/reply/forward | Yes (`cmd_send`/`cmd_reply`/`cmd_forward`, multipart attachments) | **None.** No `outlook_send_message` in either adapter file. |
| label/folder | `folder list/create`, `move <uid> <folder>` | `move <MSG_ID> --to <folder-id>` only; no folder create |
| star/flag | `star <uid>` → IMAP `\Flagged` | **None.** No Graph `flag` (flagStatus) support. |
| archive | `cmd_archive`, provider-aware (`[Gmail]/All Mail` copy+expunge) | **None.** |
| draft | `draft list/create/send` (IMAP APPEND to Drafts) | **None.** |
| unread mark | `\Seen` flag (read), `--unread` filter (inbox) | `mark <MSG_ID> [--unread]` → `isRead` PATCH |
| labels vs folders | IMAP folders; Gmail also exposes **labels as a first-class IMAP extension** (§2) | Graph "categories" (tags, independent of folder) exist as a concept but adapter never reads/writes them |

**Bottom line:** mail-cli's `outlook` IMAP/SMTP preset already gives full
Gmail-CLI parity for Outlook/365 today (Basic Auth/app-password). The Graph
adapter is a much thinner, automation-oriented, app-only + single-shared-
mailbox client (built for a bot/CI account, not "log in as me"). To make
`devhub email --provider outlook` behave like Gmail for search/send/star/
archive/label, the Graph adapter needs five new functions
(`outlook_search_messages`, `outlook_send_message`, `outlook_reply_message`,
`outlook_set_flag`, `outlook_set_categories`) — see §7.

---

## 2. Gmail grammar and label model

**Search operators** (Gmail web/API grammar): `from:`, `to:`, `cc:`, `bcc:`,
`subject:`, `label:`, `is:unread`, `is:read`, `is:starred`, `is:important`,
`has:attachment`, `has:drive`/`has:youtube` (Gmail-only, ignorable),
`after:YYYY/MM/DD`, `before:YYYY/MM/DD`, `newer_than:Nd|Nm|Ny`,
`older_than:Nd|Nm|Ny`, `filename:`, `larger:`/`smaller:` (bytes/M/K),
`in:anywhere`/`in:inbox`/`in:trash`/`in:spam`,
`category:promotions|social|updates|forums`, free text (implicit
`TEXT`/body+subject search), quoted phrases, `OR`, `-` negation, parenthesized
grouping.

**Label model:** Gmail has no folders — every message lives in one place and
carries a set of labels. System labels: `INBOX`, `SENT`, `DRAFT`, `STARRED`,
`IMPORTANT`, `TRASH`, `SPAM`, `UNREAD`, `CATEGORY_*`. **Archive = remove the
`INBOX` label** (message keeps all other labels, stays in "All Mail", just
leaves the inbox view) — this is *not* a move to a different folder, the
single most important semantic gap vs. IMAP/Graph (both folder-based, both
current backends *simulate* archive via copy+delete instead of a label
removal).

**Thread/conversation model:** Gmail groups messages into threads
(`X-GM-THRID`) shown collapsed in list views; IMAP/Graph have no native
thread concept — both mail-cli (`_mail_inbox_print_threads`,
subject-normalization heuristic) and any Graph-backed equivalent must fake it
via subject-normalization or `conversationId` (Graph messages *do* have a
real `conversationId` field, currently unused/unparsed by `_parse_message`).

**Archive semantics recap:** Gmail = drop `INBOX` label (`STORE X-GM-LABELS`
removing `\Inbox`, or via Gmail API `messages.modify
removeLabelIds:[INBOX]`). Generic IMAP/mail-cli = copy to an archive folder +
delete original (lossy: flags/labels other than the copied ones don't
necessarily survive). Graph = no "remove from Inbox, keep everywhere"
primitive; only `move` (which **deletes** the source per adapter's own
comment: "Graph creates a copy in the destination and removes the original")
— so Graph-side archive is unavoidably "move to Archive folder," never true
label-drop.

---

## 3. Backend capability skim

**`tools/mail-cli/`** (2,451 lines total, `bin/mail` = 224-line dispatcher):
dispatches `auth|inbox|read|send|reply|forward|search|folder|star|archive|
delete|move|draft|config|version|help`. Global `--account`/`--json`;
inbox/search flags `--unread --threads --wide --limit N --no-pager`.
`lib/imap.shs`: raw curl-over-IMAP-URL primitives — `mail_imap_search(folder,
criteria)` builds `SEARCH ${criteria}` verbatim (any valid IMAP SEARCH string
works today, but nothing builds Gmail's `X-GM-RAW`/`X-GM-LABELS` extension
keys yet); `store_flags`, `remove_flags`, `copy`, `delete` (flag `\Deleted` +
`EXPUNGE`), `create_folder`, `append` (drafts), `fetch_headers_range`.
`lib/inbox.shs`: `cmd_search` builds criteria as `TEXT "q" FROM "x" SUBJECT
"y" SINCE d BEFORE d` (space-joined, defaults `ALL`) — only 4 operators wired
at the CLI flag level today (`--from --subject --since --before`); no
`--label`/`--unread`/`--has-attachment` flags on `search`. `lib/folder.shs`:
`cmd_star` → `STORE +FLAGS (\Flagged)`. `cmd_archive` is **provider-aware**:
Gmail → copies to `[Gmail]/All Mail` then deletes from source folder (best
available emulation of "drop INBOX label" over generic IMAP); everything else
→ generic `Archive` folder. `cmd_move` = copy+delete to arbitrary folder.
`lib/format.shs`: table columns are UID, star-mark, FROM, SUBJECT, DATE
(relative). **Known pre-existing bug**: `mail_format_summary_line` is always
called with `flags=""` from both `cmd_inbox` and `cmd_search` — star/unread
visual markers never actually render today even though the flag-parsing code
path exists. `lib/config.shs`: account schema `{email, username,
display_name, imap_server, imap_port, smtp_server, smtp_port, tls,
password|password_cmd, provider}`; `mail_preset(provider, field)` hardcodes
host/port/tls per provider (`gmail`, `outlook`, `yahoo`, `protonmail`,
`fastmail`).

**`src/app/itf/cmd_outlook.spl`** (357 lines) + `adapter_outlook.spl` (425) +
`adapter_outlook_curl.spl` (429, curl-shellout fallback): talks to Graph v1.0
`/users/{shared_mailbox_upn}/...` (never `/me/...` — doc comment:
"client-credentials has no signed-in user") — headless/bot design, not "sign
in as your own mailbox." Auth: `outlook_client_acquire(tenant_id, client_id,
secret_env_var, mailbox_upn, cache_path)` → `oauth2_get_token` →
`oauth2_client_credentials_token` (grant_type=client_credentials only;
`std.nogc_sync_mut.oauth2` has no authorization-code or device-code function
at all). Requires Azure AD app registration + application permissions
`Mail.Read`/`Mail.ReadWrite` + an Exchange Online `ApplicationAccessPolicy`
scoping the app to one mailbox. Config in `~/.config/itf/auth.sdn` `[outlook]`
section (`tenant_id`, `client_id`, `client_secret_env` default
`GRAPH_CLIENT_SECRET`, `shared_mailbox`); secret is an env var, never inline.
Ops wired at CLI layer: `folders`, `messages <FOLDER_ID> [--filter EXPR --top
N]`, `get <MSG_ID> [--attachments]`, `move <MSG_ID> --to <DEST>`, `mark
<MSG_ID> [--unread]`. No search/send/reply/forward/star/archive/label/draft
subcommands exist. `adapter_outlook.spl` public fns: `outlook_client_acquire`,
`outlook_list_folders` (paginates `@odata.nextLink`),
`outlook_list_messages(client, folder_id, filter, top)` ("`$search` is
intentionally NOT supported here"), `outlook_get_message`, `outlook_mark_read`
(PATCH `{isRead: bool}`), `outlook_move_message` (POST `/move`
`{destinationId}`), `outlook_get_attachment_value`. `OutlookMessage` struct
only carries `id, subject, from_address, from_name, received, body_preview,
has_attachments` — no `isRead`, `flag`, `categories`, or `conversationId`
parsed even though Graph returns them when selected. `adapter_outlook_curl.spl`
is a curl-shellout mirror with even less: folders/messages/get only, no
move/mark, same app-only shared-mailbox auth.

---

## 4. Facade command surface

```
devhub email inbox   [--unread] [--threads] [--label L] [--limit N] [--wide] [--json]
devhub email read    <id> [--json] [--raw]
devhub email send    --to A [--cc A] [--bcc A] --subject S (--body B|--input FILE) [--attach F]...
devhub email reply   <id> [--body B|--input FILE] [--all]
devhub email forward <id> --to A [--body B]
devhub email search  "<gmail-query-string>" [--limit N] [--wide] [--json]
devhub email label   <id> --add L [--add L]... [--remove L]...
devhub email star    <id> [--off]
devhub email archive <id>
devhub email draft   list | create ... | send <id>
```

`devhub email` reads `provider` from `~/.config/devhub/email.sdn` (see §6 —
a new, per-facade config schema distinct from `auth.sdn`) and dispatches
every verb to one of two backend drivers:

- **`provider: gmail`** → shells to `tools/mail-cli/bin/mail` (account preset
  `gmail`, IMAP/SMTP). Search uses Gmail's native `X-GM-RAW` IMAP extension
  (§5a) — the ONLY backend where the Gmail query string needs **zero
  per-operator translation**.
- **`provider: outlook`** → calls the Graph adapter functions directly
  (in-process `.spl` call, not a subprocess) — `adapter_outlook.spl` extended
  per §7.
- **`provider: outlook_imap`** → mail-cli's own `outlook` IMAP/SMTP preset,
  for users who'd rather use app-password IMAP than register an Azure AD
  app — full parity today, no new code needed, same `X-GM-RAW`-less
  generic-IMAP-SEARCH path as Yahoo/Fastmail.

**`id` semantics differ across backends and must be resolved, not glossed
over.** IMAP UIDs (mail-cli/Gmail/`outlook_imap` path) are **per-folder**, not
globally unique — the same integer can legitimately refer to different
messages in `INBOX` vs. `Archive`. Graph `id` values (Outlook/Graph path) are
globally unique and folder-independent. Facade contract: every verb taking
`<id>` defaults `--folder INBOX` on the IMAP-backed paths (mirroring
mail-cli's own `cmd_read`/`cmd_star`/`cmd_archive` default) and accepts an
explicit `--folder` to disambiguate; the `inbox`/`search` table's `id` column
is only unique within the folder just listed, callers scripting across
folders must carry `--folder` alongside `id`. On the Graph path `--folder` is
accepted but ignored (harmless no-op) since `id` alone is already sufficient.

### Output columns (identical across all three backends)

Required column set: `id, from, subject, date, labels, unread/star markers`.
Default table shows high-signal markers as compact glyphs (★ starred, bold
unread) and appends any *non-default* labels/categories (excluding
`INBOX`/`SENT`/`UNREAD`/`STARRED`, already implied by folder context + the
glyphs) as a trailing bracketed, truncated chip list:

```
ID      ★  FROM                          SUBJECT                            DATE     LABELS
------  -  ----                          -------                            ----     ------
118392  ★  Alice Chen <alice@x.com>       Q3 planning doc                    2h ago   [Work, Important]
118391     Bob <bob@y.com>                Re: deploy window                  Jun 12   [Promotions]
```

`--wide` disables truncation on this column too (matches mail-cli's existing
`--wide` convention for `from`/`subject`). The full label/category array is
always present in `--json` and `read <id>` output, never dropped — only the
narrow default table compresses it. A bare listing with no non-default
labels renders an empty `LABELS` cell, not a placeholder dash (empty array
vs. empty string, kept structurally consistent between table and `--json`).

| Column | Gmail/mail-cli source | Outlook/Graph source |
|---|---|---|
| `id` | IMAP UID (per-folder, not globally stable — see `id` semantics note above) | Graph `id` (opaque, globally stable, immutable) |
| `from` | parsed `From:` header | `from.emailAddress.{name,address}` |
| `subject` | parsed `Subject:` header | `subject` |
| `date` | parsed `Date:` header, relativized | `receivedDateTime`, relativized (same formatter) |
| `labels` | IMAP flags mapped to pseudo-labels (`\Seen`→drop `UNREAD`, `\Flagged`→`STARRED`, folder name→label) + Gmail `X-GM-LABELS` when available, filtered to non-default for the table column | `categories[]` (tags) + folder-derived system label (`inbox` well-known-name→`INBOX` etc.), same non-default filtering |
| unread/star marker | `\Seen`/`\Flagged` (bug today: not wired into the render call — needs the one-line fix noted in §3) | `isRead`/`flag.flagStatus` (needs adapter to parse+return these — currently dropped) |

---

## 5. Search: Gmail operator → per-backend translation

### 5a. Gmail path — verbatim passthrough via X-GM-RAW (primary)

Real Gmail IMAP servers implement the documented `X-GM-EXT-1` capability,
including the `X-GM-RAW` search key, which accepts **the exact same query
grammar as the Gmail search box**, verbatim. Highest-fidelity option; needs
one new mail-cli function (does not exist yet — today `mail_imap_search` only
issues plain `SEARCH ${criteria}`):

```bash
# lib/imap.shs — new function (facade-only, only invoked when provider=gmail)
mail_imap_search_raw() {   # $1=folder $2=gmail-query-string
  local folder="${1:-INBOX}" query="$2"
  local escaped; escaped=$(printf '%s' "$query" | sed 's/\\/\\\\/g; s/"/\\"/g')
  _mail_curl -s --url "$(_imap_url "$folder")" --user "${MAIL_ACCT_USERNAME}:${MAIL_ACCT_PASSWORD}" \
    --request "SEARCH X-GM-RAW \"${escaped}\"" 2>/dev/null \
    | grep -oE '\* SEARCH [0-9 ]+' | sed 's/\* SEARCH //'
}
```

`devhub email search "from:alice subject:invoice is:unread"` on a Gmail
account becomes literally `SEARCH X-GM-RAW "from:alice subject:invoice
is:unread"` — no translation table needed, every Gmail operator (including
ones with no IMAP equivalent at all — `category:`, `larger:`, `has:drive`,
`newer_than:`) works because Gmail's own server parses the query.

### 5b. Fallback path — non-Gmail IMAP, per-operator translation

Used for non-Gmail IMAP (Yahoo/Fastmail/generic/`outlook_imap` preset) or if
`X-GM-RAW` is ever unavailable:

| Gmail operator | IMAP SEARCH term | Notes |
|---|---|---|
| `from:X` | `FROM "X"` | substring match on header, IMAP servers vary on address-only vs. display-name matching |
| `to:X` | `TO "X"` | |
| `cc:X` | `CC "X"` | not a `cmd_search` flag today — needs adding |
| `bcc:X` | `BCC "X"` | Bcc header usually stripped server-side; rarely matches |
| `subject:X` | `SUBJECT "X"` | |
| free text / `"phrase"` | `TEXT "X"` | searches headers+body |
| `is:unread` | `UNSEEN` | |
| `is:read` | `SEEN` | |
| `is:starred` | `FLAGGED` | |
| `is:important` | *(no IMAP equivalent)* | fallback: drop the term, warn on stderr — no standard flag for "important" outside Gmail |
| `has:attachment` | *(no native key)* | fallback: best-effort `HEADER "Content-Type" "multipart/mixed"` heuristic (false negatives on multipart/alternative-with-attachment, false positives on multipart/alternative HTML+text) — document as lossy |
| `after:YYYY/MM/DD` | `SINCE dd-Mon-yyyy` | IMAP date-only, no time-of-day |
| `before:YYYY/MM/DD` | `BEFORE dd-Mon-yyyy` | |
| `newer_than:Nd` | `SINCE <today-N-days>` (computed client-side) | also support `Nm`/`Ny` (months/years) |
| `older_than:Nd` | `BEFORE <today-N-days>` | |
| `label:X` | folder select — run search against IMAP folder `X` instead of `INBOX` | only works when label==folder name; lossy for true multi-label Gmail messages when not using `X-GM-RAW`/`X-GM-LABELS` |
| `in:anywhere` | search all folders (loop `folder list` + per-folder `SEARCH`, union) | expensive; document as opt-in (`--all-folders`) |
| `in:trash`/`in:spam` | select `Trash`/`Spam` folder | provider-specific folder names (Gmail: `[Gmail]/Trash`, `[Gmail]/Spam`) |
| `category:X` | *(no IMAP equivalent)* | unsupported — return error, suggest `X-GM-RAW` (Gmail-only) instead |
| `filename:X` | *(no IMAP equivalent)* | unsupported without MIME-structure fetch — fallback: fetch `BODYSTRUCTURE`, filter client-side (expensive; flag as `--slow` opt-in) |
| `larger:N`/`smaller:N` | *(no IMAP equivalent)* | fallback: `FETCH RFC822.SIZE` after UID search, filter client-side |
| `-term` (negation) | `NOT <term>` | IMAP `SEARCH` supports `NOT` natively |
| `OR` | `OR <term1> <term2>` | IMAP `SEARCH` `OR` takes exactly 2 args — n-ary Gmail `OR` chains must right-fold into nested `OR` |

### 5c. Outlook/Graph path — $search KQL (primary) and $filter (structured list-scoping)

Microsoft's Graph mail search supports a documented **KQL-style
property-scoped syntax inside `$search`** itself — e.g.
`$search="from:janedoe@contoso.com subject:conference"` — over a fixed,
documented property set: `from`, `to`, `cc`, `bcc`, `subject`, `body`,
`participants` (from+to+cc+bcc combined), `received` (date, `..` range),
`sent` (date range), `hasattachment` (bool), `importance`, `category`, `size`
(byte range, `..`), `kind`, `attachment` (filename/content). **No live
network call was made to confirm this against the current API surface** —
verify the exact property list against Microsoft's "Search for messages" /
"Use $search with Outlook" reference before shipping; treat the table below
as the intended target, not a tested contract.

This makes the two Graph mechanisms cleanly non-overlapping by construction,
resolving the "`$filter`+`$search` are mutually exclusive" constraint the
adapter's own comment already documents — because they're now used for
disjoint verbs, not a per-query choice:
- **`search` verb → `$search` KQL only.** Free text plus any property-scoped
  qualifier Gmail exposes an analog for goes into one `$search` string — a
  near-verbatim passthrough analogous to Gmail's `X-GM-RAW`, not a
  term-by-term `$filter` translation.
- **Structured listing filters (`inbox --unread`, `is:starred` as a *list*
  modifier rather than part of a `search` query) → `$filter`**, since
  `isRead`/`flag.flagStatus` are not in the documented `$search` KQL property
  set. These two verbs never need to combine in one request, so the
  exclusivity rule never bites.

Advanced `$filter` operators (`contains`, `any` lambda, `startsWith` on
non-default-indexed properties — still needed for `inbox --label X` on
non-system categories) require the `ConsistencyLevel: eventual` request
header plus `$count=true` query param — a real, non-optional Graph
requirement; add it to `_outlook_get`/`_outlook_attach_auth` whenever these
operators are used.

| Gmail operator | Graph `$search` KQL term (primary, `search` verb) | Graph `$filter` (secondary, structured list-scoping only) |
|---|---|---|
| `from:X` | `from:X` | `from/emailAddress/address eq 'X'` (exact-match fallback if KQL unavailable) |
| `to:X` | `to:X` | `toRecipients/any(r:r/emailAddress/address eq 'X')` (needs `ConsistencyLevel: eventual`) |
| `cc:X` | `cc:X` | `ccRecipients/any(...)` (same header requirement) |
| `bcc:X` | `bcc:X` (documented KQL property; unclear if populated for received mail) | *(no reliable `$filter` equivalent)* |
| `subject:X` | `subject:X` | `contains(subject,'X')` (needs `ConsistencyLevel: eventual`) |
| free text / `"phrase"` | bare term / quoted phrase, combine with `AND`/`OR`/`NOT` natively | n/a |
| `is:unread` | *(not in the KQL property set — route through `$filter`, not `$search`)* | `isRead eq false` |
| `is:read` | *(same)* | `isRead eq true` |
| `is:starred` | *(same — `flag.flagStatus` not KQL-searchable)* | `flag/flagStatus eq 'flagged'` (needs new `outlook_set_flag`/read support — not parsed today) |
| `is:important` | `importance:high` | `importance eq 'high'` (Graph's concept differs from Gmail's ML-driven "important" — approximate, not a true equivalent, either mechanism) |
| `has:attachment` | `hasattachment:true` | `hasAttachments eq true` (direct field, already parsed by `_parse_message`) |
| `after:YYYY/MM/DD` | `received:YYYY-MM-DD..` (open-ended range) | `receivedDateTime ge YYYY-MM-DDT00:00:00Z` |
| `before:YYYY/MM/DD` | `received:..YYYY-MM-DD` | `receivedDateTime le YYYY-MM-DDT00:00:00Z` |
| `newer_than:Nd` | `received:<today-N-days>..` (date computed client-side) | same, via `$filter` |
| `label:X` | if `X` ∈ {INBOX,SENT,DRAFT,TRASH,STARRED} → route to the matching well-known folder (`mailFolders('inbox')`, `('sentitems')`, `('drafts')`, `('deleteditems')`, or the `is:starred` term above) instead of any query string; else → `category:X` in `$search` KQL, or `$filter=categories/any(c:c eq 'X')` as the structured-list fallback (Graph "categories" are the nearest Gmail-label analog — free-form, message can carry many, independent of folder) | needs new `outlook_set_categories`/parse support either way |
| `in:anywhere` | omit folder scoping — query `/users/{upn}/messages` directly instead of `/mailFolders/{id}/messages` | same |
| `category:X` (Gmail auto categories: promotions/social/updates/forums) | *(no Graph equivalent — Gmail ML classification, not exposed via Graph)* | unsupported, error clearly |
| `filename:X` | `attachment:X` (documented KQL property, searches attachment name/content) | `$filter=attachments/any(a:a/name eq 'X')` fallback, requires `$expand=attachments` + `ConsistencyLevel: eventual` — expensive, opt-in |
| `larger:N`/`smaller:N` | `size:N..` / `size:..N` (documented KQL byte-range property — direct support, not lossy) | *(no `size` property in `$filter` on the `message` resource — `search` verb is the only path for this operator)* |
| `-term` | `NOT term` (native KQL) | `not(...)` function |
| `OR` | `A OR B` (native, n-ary) | `(A) or (B)` |

**Remaining gap, honestly scoped:** the `search` verb still cannot combine a
KQL-eligible term (`from:`, `subject:`, `size:`, etc.) with an
`isRead`/`flag`-based term in one request, since those two properties are
`$filter`-only, not in the KQL set. Defined fallback: if a query mixes
KQL-eligible and `$filter`-only terms, run the KQL `$search` first (capped at
`--limit × 4`) then apply the `$filter`-only predicates as an in-process
post-filter on the returned `OutlookMessage` fields. Re-verify once the KQL
property list is confirmed live.

---

## 6. Label/star/archive verb mapping

| Facade verb | Gmail/mail-cli (IMAP) | Outlook/Graph | Lossy cases |
|---|---|---|---|
| `label <id> --add L` | if `L` is a system label handled specially (`STARRED`→`\Flagged`); else `mail_imap_copy` into IMAP folder `L` (does **not** remove from source — no true multi-label op without `X-GM-LABELS`) | new `outlook_set_categories(client, msg_id, add: [L])` → `PATCH {"categories": [...]}` (Graph categories are a full-replace array, not add/remove — read-modify-write required) | On generic IMAP, `--add` before `X-GM-LABELS` support ships is really "copy to folder," i.e. duplicates the message rather than tagging it — must be documented, not silently presented as true Gmail-label semantics |
| `label <id> --remove L` | Gmail-only via `X-GM-LABELS` `STORE` (new fn needed, mirrors `mail_imap_search_raw`); non-Gmail IMAP has no concept of "remove a label that isn't the folder" | same read-modify-write `categories` PATCH, filtering `L` out | Removing `INBOX` specifically **is** archive (see below) — must special-case so `label --remove INBOX` and `archive` produce the same effect on Gmail |
| `star <id>` | `STORE +FLAGS (\Flagged)` (exists, `cmd_star`) | new `outlook_set_flag(client, msg_id, true)` → `PATCH {"flag": {"flagStatus": "flagged"}}` | none — both sides have a native single-message flag |
| `star <id> --off` | `STORE -FLAGS (\Flagged)` (mail-cli has `mail_imap_remove_flags`, not currently wired to a CLI flag — needs `--off` added to `cmd_star`) | `PATCH {"flag": {"flagStatus": "notFlagged"}}` | none |
| `archive <id>` | **Gmail path, ideal:** `STORE X-GM-LABELS -("\\Inbox")` (true label-drop, matches Gmail semantics exactly, no copy/delete, no data duplication) — new function needed, not what `cmd_archive` does today. **Gmail path, current mail-cli behavior:** copy to `[Gmail]/All Mail` + delete from `INBOX` (functionally similar end-state on Gmail specifically, but semantically copy+delete, not label-drop — flags set after copy may not be preserved by all servers). **Non-Gmail IMAP:** copy to `Archive` + delete (`cmd_archive` today, generic branch) | `outlook_move_message(msg_id, dest: "archive")` (Graph's well-known folder name `archive` resolves via `/mailFolders/archive`) — Graph's own semantics are already "copy to dest, delete source" per the adapter's doc comment, so this is a true 1:1, no facade-level compromise needed | Folder-based archive is fundamentally lossy vs. Gmail's label-drop when the message also had non-system labels/categories that a naive copy+delete might not carry over — recommend the facade always prefer the `X-GM-LABELS` route on Gmail once implemented, falling back to copy+delete only for non-Gmail IMAP and Graph |

---

## 7. Provider config schema — `~/.config/devhub/email.sdn`

**Note on config layout:** this is a new, dedicated multi-account config file
for the `email` facade, separate from `~/.config/itf/auth.sdn` (which today
holds single-section-per-backend config for Confluence/Jira/MinIO/Outlook).
See `devhub_overview.md` §4 for how this reconciles with the repo-wide config
baseline — treat `email.sdn` as additive, not a replacement for `auth.sdn`'s
existing `[outlook]` section, until the two are formally reconciled.

SDN (this repo's stated config format, not JSON/YAML), one `[account]`-style
block per configured identity, mirroring mail-cli's `config.json` schema plus
a `provider` switch and, for Outlook, the same `[outlook]` fields
`cmd_outlook.spl` already reads from `~/.config/itf/auth.sdn`:

```
default_account: "work-gmail"

accounts:
  work-gmail:
    provider: gmail            # → dispatches to tools/mail-cli/bin/mail, preset "gmail"
    email: "me@company.com"
    password_cmd: "pass show mail/work-gmail"   # app password, never stored inline

  work-outlook:
    provider: outlook          # → dispatches to the Graph adapter (adapter_outlook.spl)
    tenant_id: "11111111-2222-3333-4444-555555555555"
    client_id: "66666666-7777-8888-9999-aaaaaaaaaaaa"
    client_secret_env: "GRAPH_CLIENT_SECRET"    # secret lives in the env, not this file
    shared_mailbox: "me@company.com"            # Graph /users/{upn} target

  personal-outlook-imap:
    provider: outlook_imap      # → dispatches to mail-cli, preset "outlook" (IMAP/SMTP)
    email: "me@outlook.com"
    password_cmd: "pass show mail/personal-outlook"
```

`devhub email --account work-outlook inbox` resolves `provider: outlook`,
loads `[tenant_id, client_id, client_secret_env, shared_mailbox]`, and calls
`outlook_client_acquire` exactly as `cmd_outlook.spl`'s `_acquire_client()`
does today — "configure once" = do the Azure AD app registration +
`ApplicationAccessPolicy` once, after which every `devhub email` verb Just
Works against that mailbox with Gmail-style output.

**App-only OAuth caveat (must not be silently glossed over):** this is
honest about matching the *existing* Graph adapter's auth model (app-only,
one shared mailbox) — it is **not** "sign in with your personal Microsoft
account interactively," because no delegated/device-code OAuth flow exists
in this codebase (`std.nogc_sync_mut.oauth2` has only
`oauth2_client_credentials_token`). If genuine personal-account delegated
login is required, that's new work: a device-code flow
(`https://login.microsoftonline.com/{tenant}/oauth2/v2.0/devicecode` → poll
`.../token` with `grant_type=urn:ietf:params:oauth:grant-type:device_code`)
needs to be added to `std.*.oauth2` before `devhub email auth login
--provider outlook --personal` can exist — flagged as an open item, not
built silently into the config schema.

---

## 8. `adapter_outlook` gap checklist

New code needed beyond routing/config, in priority order:

1. `lib/imap.shs` (mail-cli): `mail_imap_search_raw` (`X-GM-RAW` passthrough,
   Gmail only) + wire `mail_format_summary_line`'s flag argument through from
   a real `FETCH ... FLAGS` call (currently always `""`, pre-existing bug,
   blocks unread/star markers in any listing).
2. `lib/inbox.shs` / `lib/folder.shs` (mail-cli): add `--cc`, `label`,
   `--off` (unstar) flags; add `label --add/--remove` dispatch (Gmail:
   `X-GM-LABELS` STORE; generic IMAP: copy-only with a documented caveat).
3. `adapter_outlook.spl`: add `outlook_search_messages` (`$search`, unscoped
   `/messages`), `outlook_send_message` (POST `/sendMail`),
   `outlook_reply_message` (POST `/messages/{id}/reply`), `outlook_set_flag`
   (PATCH `flag.flagStatus`), `outlook_set_categories` (PATCH `categories`,
   read-modify-write); extend `OutlookMessage` to parse `isRead`,
   `flag.flagStatus`, `categories[]`, `conversationId`; add
   `ConsistencyLevel: eventual` header + `$count=true` support to
   `_outlook_get` for advanced-query calls.
4. `cmd_outlook.spl`: wire the above into `search|send|reply|forward|star|
   label|archive|draft` subcommands (currently only `folders|messages|get|
   move|mark` exist).
5. New `devhub` entrypoint that owns `~/.config/devhub/email.sdn` parsing
   and routes to (2)/(4) per `provider`.
