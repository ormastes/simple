# Microsoft Graph Mail API — Research Note (April 2026)

Audience: adapter author adding an Outlook/Exchange backend to the `tools/mail-cli` dispatcher.
The existing IMAP backend surface (imap.shs) defines the contract: list-folders, search, fetch-headers,
fetch-body, list-attachments, store/remove flags (mark-read), copy/move, create-folder.

---

## 1. API Surface and v2.0 Retirement

### Status of Outlook REST v2.0

The legacy `outlook.office.com/api/v2.0` endpoint **was fully decommissioned in March 2024**
(announced timeline; executed as announced). The compare-graph page states:

> "The Outlook REST endpoints will be fully decommissioned in March 2024.
> Migrate existing apps to use Microsoft Graph."

Source: https://learn.microsoft.com/en-us/outlook/rest/compare-graph

### Correct surface in 2026

**Microsoft Graph v1.0** at `https://graph.microsoft.com/v1.0/` is the only supported REST surface
for mail. The beta endpoint (`/beta`) exists for preview features but must not be used in production
adapters. All endpoints in this note are v1.0.

---

## 2. OAuth2 Flow and Scopes

### 2.1 Flow recommendation for a daemon/CLI tool

Two options exist; they serve different trust models:

| Flow | Entra ID grant | Token type | Shared-inbox access |
|---|---|---|---|
| **Client Credentials** (app-only) | `client_credentials` | No user context | Yes, via `ApplicationAccessPolicy` |
| **Device Code** (delegated) | `urn:ietf:params:oauth:grant-type:device_code` | User refresh token | Yes, if user has Full Access to shared mailbox |

**Recommendation: Client Credentials (app-only)** for a daemon that ingests a shared bug-report inbox.

Rationale:
- No interactive sign-in required; no refresh-token rotation risk from user leaving.
- Admin scopes the app to exactly the shared mailbox via `New-ApplicationAccessPolicy` (Exchange PowerShell) even though the `Mail.Read` application permission would otherwise grant access to all mailboxes in the tenant.
- Refresh tokens from Device Code flow expire after 90 days of non-use and rotate on each use; a daemon that runs infrequently can silently lose access. Client credentials use a client secret or certificate that the admin controls and rotates on their own schedule.

Source: https://learn.microsoft.com/en-us/azure/active-directory/develop/v2-oauth2-client-creds-grant-flow

### 2.2 Scopes

| Permission | Category | Admin consent | Notes |
|---|---|---|---|
| `Mail.Read` | Application | Yes | Read all mailboxes without signed-in user. Sufficient for read-only ingest. Use with client credentials. |
| `Mail.ReadWrite` | Application | Yes | Required for mark-as-read (PATCH isRead) and move. |
| `Mail.Read` | Delegated | No | Reads signed-in user's own mailbox only. |
| `Mail.Read.Shared` | Delegated | No | Reads mail the signed-in user can access including shared mailboxes. Work/school accounts only. Not available as Application permission. |
| `Mail.ReadWrite.Shared` | Delegated | No | Same as above plus write. |

**For shared-inbox ingest (daemon)**:
- Use **`Mail.Read` application** + `ApplicationAccessPolicy` to pin the app to the target mailbox.
- Add **`Mail.ReadWrite` application** if mark-as-read or move is needed.
- `Mail.Read.Shared` is a *delegated-only* permission; it is not available for app-only flows and is not the right choice for a daemon.

Source: https://learn.microsoft.com/en-us/graph/permissions-reference (Mail.* section)

### 2.3 Token endpoint (client credentials)

```
POST https://login.microsoftonline.com/{tenant_id}/oauth2/v2.0/token
Content-Type: application/x-www-form-urlencoded

grant_type=client_credentials
&client_id={app_id}
&client_secret={secret}
&scope=https://graph.microsoft.com/.default
```

Response contains `access_token` (Bearer JWT, 1-hour expiry) and `expires_in`. No refresh token is
issued for client credentials; re-request a new token before expiry.

### 2.4 Device Code flow (fallback / personal accounts)

```
POST https://login.microsoftonline.com/{tenant}/oauth2/v2.0/devicecode
client_id={app_id}&scope=Mail.Read offline_access
```

Poll until user completes browser sign-in; receive `access_token` + `refresh_token`.
Use `offline_access` to get a refresh token. Refresh tokens rotate: each use issues a new one.
Personal accounts: 90-day sliding window. Work/school: configurable by admin, default 90 days.

Source: https://learn.microsoft.com/en-us/azure/active-directory/develop/v2-oauth2-device-code

---

## 3. Endpoints

All paths are relative to `https://graph.microsoft.com/v1.0`.
Add `Authorization: Bearer {token}` to every request.

### 3.1 List Mail Folders

```
GET /me/mailFolders
GET /users/{id|upn}/mailFolders
```

Query params: `$top` (max 250), `$select`, `$filter`, `includeHiddenFolders=true`.

Response shape:
```json
{
  "value": [
    {
      "id": "AAM...",
      "displayName": "Inbox",
      "parentFolderId": "...",
      "childFolderCount": 2,
      "unreadItemCount": 5,
      "totalItemCount": 120,
      "isHidden": false
    }
  ],
  "@odata.nextLink": "..."
}
```

Well-known folder names usable in place of id: `inbox`, `drafts`, `sentitems`, `deleteditems`,
`archive`, `junkemail`, `outbox`, `recoverableitemsdeletions`.

Source: https://learn.microsoft.com/en-us/graph/api/user-list-mailfolders

### 3.2 List Messages in Folder

```
GET /me/mailFolders/{folderId}/messages
GET /users/{id|upn}/mailFolders/{folderId}/messages
```

Key query params:

| Param | Example | Notes |
|---|---|---|
| `$top` | `$top=50` | Default 10, max 1000. Keep ≤100 to avoid HTTP 504. |
| `$select` | `$select=id,subject,from,receivedDateTime,isRead,hasAttachments` | Always use — cuts payload 80%. |
| `$filter` | `$filter=isRead eq false` | OData filter. Works on indexed props. |
| `$search` | `$search="subject:bug report"` | KQL full-text search. Cannot combine with `$filter`. |
| `$orderby` | `$orderby=receivedDateTime desc` | Cannot use with `$search`. |

Response: `{ "value": [ {message objects} ], "@odata.nextLink": "..." }`

Source: https://learn.microsoft.com/en-us/graph/api/user-list-messages

### 3.3 Get Single Message

```
GET /me/messages/{id}
GET /users/{id|upn}/messages/{id}
```

Response: full `message` resource including `body` (contentType + content), `toRecipients`,
`from`, `subject`, `receivedDateTime`, `isRead`, `hasAttachments`, `attachments` (if `$expand=attachments`).

To get body + attachments in one call:
```
GET /me/messages/{id}?$expand=attachments&$select=id,subject,body,from,receivedDateTime,isRead,attachments
```

Source: https://learn.microsoft.com/en-us/graph/api/message-get

### 3.4 List Attachments

```
GET /me/messages/{id}/attachments
GET /users/{id|upn}/messages/{id}/attachments
```

Response: `{ "value": [ { "id", "name", "contentType", "size", "contentBytes" (base64), "@odata.type" } ] }`

`@odata.type` values: `#microsoft.graph.fileAttachment`, `#microsoft.graph.itemAttachment`,
`#microsoft.graph.referenceAttachment`.

For attachments > 3 MB: `contentBytes` is not returned inline; use the upload-session approach
for sending, and for reading use the individual attachment endpoint:
```
GET /me/messages/{id}/attachments/{attachmentId}/$value
```
to stream raw bytes.

Source: https://learn.microsoft.com/en-us/graph/api/message-list-attachments

### 3.5 Mark Read / Update (PATCH isRead)

```
PATCH /me/messages/{id}
PATCH /users/{id|upn}/messages/{id}
Content-Type: application/json

{ "isRead": true }
```

Requires `Mail.ReadWrite` permission. Returns updated `message` object (200 OK).
Other patchable fields (when `isDraft=false`): `categories`, `flag`, `inferenceClassification`.

Source: https://learn.microsoft.com/en-us/graph/api/message-update

### 3.6 Move Message

```
POST /me/messages/{id}/move
POST /users/{id|upn}/messages/{id}/move
Content-Type: application/json

{ "destinationId": "inbox" }
```

`destinationId` accepts either a folder id or a well-known name string.
Creates a new copy in destination and removes original. Returns new `message` object (201 Created).
Requires `Mail.ReadWrite`.

Source: https://learn.microsoft.com/en-us/graph/api/message-move

### 3.7 Send Message

```
POST /me/sendMail
POST /users/{id|upn}/sendMail
Content-Type: application/json

{
  "message": {
    "subject": "...",
    "body": { "contentType": "Text", "content": "..." },
    "toRecipients": [ { "emailAddress": { "address": "..." } } ]
  },
  "saveToSentItems": true
}
```

Returns 202 Accepted (no body). Requires `Mail.Send` (delegated or application).

Source: https://learn.microsoft.com/en-us/graph/api/user-sendmail

---

## 4. Attachments Larger Than 3 MB

**Threshold is 3 MB** (not 4 MB). Inline `contentBytes` upload via POST to `/attachments` works
only for files < 3 MB. For files **between 3 MB and 150 MB** use an upload session.

### Sending large attachments

```
POST /me/messages/{draftId}/attachments/createUploadSession
Content-Type: application/json

{
  "AttachmentItem": {
    "attachmentType": "file",
    "name": "report.zip",
    "size": 8388608
  }
}
```

Response: `{ "uploadUrl": "https://outlook.office.com/api/...uploadSession", "expirationDateTime": "...", "nextExpectedRanges": ["0-"] }`

Then PUT ranges sequentially (up to **4 MB per PUT**):
```
PUT {uploadUrl}
Content-Length: 4194304
Content-Range: bytes 0-4194303/8388608
[binary data]
```

Final PUT response is 201 Created with the attachment id.

Source: https://learn.microsoft.com/en-us/graph/api/attachment-createuploadsession

### Reading large attachments

For **incoming** attachments > 3 MB, stream via:
```
GET /me/messages/{id}/attachments/{attachmentId}/$value
```
Returns raw binary stream. The metadata endpoint (`/attachments/{id}` without `$value`) still works
but omits `contentBytes`.

---

## 5. Pagination, Throttling, and Rate Limits

### 5.1 Pagination

Microsoft Graph uses `@odata.nextLink` for server-driven paging.

- Default page size: 10 messages (for `/messages`).
- Use `$top` to set page size (1–1000 for messages).
- When more pages exist the response includes `"@odata.nextLink": "https://graph.microsoft.com/v1.0/..."`.
- Follow `@odata.nextLink` verbatim — do not extract `$skip` or modify the URL.
- Loop until `@odata.nextLink` is absent.

Source: https://learn.microsoft.com/en-us/graph/paging

### 5.2 Throttling

When a throttling threshold is exceeded:
- HTTP **429 Too Many Requests** is returned.
- Response header `Retry-After: {seconds}` specifies how long to wait before retrying.
- Must respect `Retry-After`; retrying before the interval will continue to receive 429.

Exchange Online (mail) specific limits (from throttling-limits page):
- Per-app + per-mailbox: **10,000 API requests per 10 minutes**.
- Per-app across all mailboxes: varies; large-volume extraction should use **Microsoft Graph Data Connect** instead of REST.
- Concurrent connections: limited; back off with exponential retry.

Retry strategy for adapter:
1. On 429: read `Retry-After`, sleep that many seconds, retry once.
2. On second 429: exponential backoff with jitter, max 3 retries.
3. Log and surface error if all retries fail.

Source: https://learn.microsoft.com/en-us/graph/throttling
Source: https://learn.microsoft.com/en-us/graph/throttling-limits

---

## 6. Refresh Token Storage

### Client credentials (recommended path)

Client credentials flow does **not** issue a refresh token. The adapter stores:
- `client_id`, `tenant_id` — not secret; store in `~/.config/itf/outlook.sdn`.
- `client_secret` or path to certificate private key — **secret**. Options:
  - Environment variable `GRAPH_CLIENT_SECRET` (simplest for CI/daemon).
  - Secret store (e.g., system keyring via `secret-tool`, or HashiCorp Vault).
  - Encrypted file: `~/.config/itf/outlook_secret.sdn` with 0600 permissions.
- Cached access token + `expires_at` — store in `~/.config/itf/outlook_token_cache.sdn`. Re-request when within 60 seconds of expiry.

### Device code / delegated path (fallback)

If using delegated flow, store in a **separate file** from Jira auth:
`~/.config/itf/outlook_auth.sdn`

Reason: Microsoft tokens rotate on every refresh (sliding window). Storing in the same file as
Jira risks a write-conflict if two tools refresh simultaneously. Separate file + atomic write
(write temp + rename) prevents corruption.

Fields to store:
```
# outlook_auth.sdn
access_token: "eyJ..."
refresh_token: "0.A..."
expires_at: 1745000000   # unix epoch seconds
token_type: "Bearer"
scope: "Mail.Read offline_access"
```

Refresh token rotation: after each refresh, the old refresh token is invalidated within a short
window. Always persist the new refresh token before using the new access token.

---

## 7. Webhooks / Change Notifications (Subscriptions)

### Creating a subscription

```
POST https://graph.microsoft.com/v1.0/subscriptions
Content-Type: application/json

{
  "changeType": "created,updated",
  "notificationUrl": "https://your-public-endpoint.example.com/graph/notify",
  "resource": "/me/mailFolders/inbox/messages",
  "expirationDateTime": "2026-04-29T18:00:00Z",
  "clientState": "secretClientState"
}
```

Requires `Mail.Read` (minimum) for the resource. Returns subscription object with `id`.

### Lifetime limits

| Resource | Max expiration |
|---|---|
| `me/messages` / `users/{id}/messages` | **4,230 minutes** (~2.9 days) |
| `me/mailFolders` | 4,230 minutes |

Subscriptions must be renewed before expiry via:
```
PATCH https://graph.microsoft.com/v1.0/subscriptions/{id}
{ "expirationDateTime": "{new_datetime}" }
```

### Validation handshake

On subscription creation, Graph sends a POST to `notificationUrl` with a `validationToken` query
parameter. The endpoint must echo the token as plain text (200 OK) within 10 seconds. If it fails,
the subscription is not created.

### CLI implication

A CLI tool running on a developer machine **cannot** serve a public HTTPS webhook. Therefore:
- **Phase 1 (now)**: implement polling using `list messages` with `$filter=isRead eq false` or
  `$filter=receivedDateTime ge {last_checked}`.
- **Phase 2 (future)**: subscriptions when a persistent relay/proxy is available.

Source: https://learn.microsoft.com/en-us/graph/api/subscription-post-subscriptions

---

## IMAP-to-Graph Operation Mapping

| IMAP operation (imap.shs) | Graph equivalent |
|---|---|
| `mail_imap_list_folders` | `GET /users/{upn}/mailFolders` |
| `mail_imap_search folder criteria` | `GET /users/{upn}/mailFolders/{id}/messages?$filter=...` or `$search=` |
| `mail_imap_fetch_headers folder uid` | `GET /users/{upn}/messages/{id}?$select=id,subject,from,receivedDateTime,isRead` |
| `mail_imap_fetch_body folder uid` | `GET /users/{upn}/messages/{id}?$select=id,body&$expand=attachments` |
| `mail_imap_store_flags ... \\Seen` | `PATCH /users/{upn}/messages/{id}` `{ "isRead": true }` |
| `mail_imap_remove_flags ... \\Seen` | `PATCH /users/{upn}/messages/{id}` `{ "isRead": false }` |
| `mail_imap_copy folder uid dest` | `POST /users/{upn}/messages/{id}/copy` `{ "destinationId": "..." }` |
| `mail_imap_copy` + `mail_imap_delete` (move) | `POST /users/{upn}/messages/{id}/move` `{ "destinationId": "..." }` |
| `mail_imap_create_folder` | `POST /users/{upn}/mailFolders` `{ "displayName": "..." }` |
| `mail_imap_delete` | `DELETE /users/{upn}/messages/{id}` (moves to Deleted Items) |

**Note on search**: Graph does not combine `$search` and `$filter` in the same request. For
criteria that mix full-text and property filters, run two queries or use KQL syntax within `$search`.

---

## Decisions for Adapter

1. **OAuth2 flow**: Use **client credentials** (`grant_type=client_credentials`) with `Mail.Read`
   + `Mail.ReadWrite` application permissions. Restrict to the shared inbox mailbox via
   `New-ApplicationAccessPolicy` in Exchange Online PowerShell. This eliminates user-interaction
   and refresh-token rotation risk for a daemon.

2. **Scopes**: `Mail.Read` for list/search/get, `Mail.ReadWrite` for mark-read and move.
   Do not request `Mail.Read.Shared` — it is delegated-only and irrelevant for client credentials.

3. **Attachment threshold**: **3 MB** (not 4 MB). Inline base64 for < 3 MB; upload-session
   (`createUploadSession` + sequential PUTs of up to 4 MB each) for 3 MB – 150 MB.
   For reading large attachments: stream via `GET .../attachments/{id}/$value`.

4. **Pagination**: Always follow `@odata.nextLink` verbatim. Set `$top=50` and `$select` to the
   minimum fields needed to avoid HTTP 504 on large mailboxes.

5. **Throttling**: Respect `Retry-After` on HTTP 429. Implement exponential backoff (max 3 retries).
   Stay well under 10,000 requests/10 min per mailbox.

6. **Token storage**: Client credentials — cache access token in `~/.config/itf/outlook_token_cache.sdn`;
   store secret in env var `GRAPH_CLIENT_SECRET` or encrypted file at 0600. Delegated fallback —
   use `~/.config/itf/outlook_auth.sdn` (separate from Jira), atomic write (tmp + rename) to survive
   token rotation race conditions.

7. **Webhooks**: Defer to Phase 2. Phase 1 adapter polls with `$filter=receivedDateTime ge {ts}`
   on a configurable interval. No public endpoint needed.

8. **Base URL for all calls**: `https://graph.microsoft.com/v1.0/users/{shared_mailbox_upn}/...`
   (not `/me/...`) when using client credentials, since there is no signed-in user context.
