# Bitbucket Cloud REST API 2.0 — Research Note (April 2026)

**Purpose:** Design reference for `src/app/itf/adapter_bitbucket.spl` supporting the `/spipe`
3-level review pipeline (Level 2: bot-approve + poll-merge; Level 3: comment-only, human
approves). Target: Bitbucket Cloud free tier.

**Sources verified:** All endpoints confirmed from live Atlassian developer docs fetched
2026-04-26. The Bitbucket Cloud API base URL is `https://api.bitbucket.org/2.0`.

---

## 1. Authentication

### 1.1 Current Auth Landscape (April 2026)

Bitbucket Cloud has three active token types and one deprecated one:

| Type | Status | Header format | Expiry |
|------|--------|---------------|--------|
| **App Passwords** | **Deprecated** — use API tokens | Basic `user:app-password` | Never (legacy) |
| **API Tokens** | Current replacement for App Passwords | Basic `email:api-token` | Required, max 1 year |
| **Repository Access Tokens** | Machine-scoped, no user tie | Bearer `<token>` | Required |
| **Workspace Access Tokens** | Workspace-scoped, no user tie | Bearer `<token>` | Required |
| **OAuth 2.0** | Full 3-LO flow | Bearer `<access_token>` | 1 hour (refresh available) |

Source: https://developer.atlassian.com/cloud/bitbucket/rest/intro/#authentication

### 1.2 App Password Deprecation Status

**App Passwords are deprecated as of April 2026.** The official docs now state:

> "App passwords are deprecated. Use API tokens."

Source: https://developer.atlassian.com/cloud/bitbucket/rest/intro/#app-passwords

The deprecation is active — new integrations must not use App Passwords.

### 1.3 API Tokens (Recommended for bot/CI use)

API Tokens are the current long-term replacement for App Passwords. Key properties:
- Authenticated via **HTTP Basic** per RFC-2617: username = Atlassian email address, password = token.
- Header: `Authorization: Basic base64(email:token)`
- Require an expiry date at creation (maximum 1 year).
- Cannot be viewed or modified after creation (disposable — replace rather than rotate).
- Support privilege scopes (identical scope names to OAuth 2.0).
- Can be scoped to a specific Bitbucket Cloud workspace.
- Do **not** require two-step verification.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/intro/#api-tokens
Source: https://support.atlassian.com/bitbucket-cloud/docs/api-tokens/

### 1.4 Repository Access Tokens (Alternative for scoped machine use)

- Created at repository level by a repo or workspace admin.
- Authenticated via **HTTP Bearer**: `Authorization: Bearer <token>`
- Available scopes for repo access tokens:
  - `repository`, `repository:write`, `repository:delete`
  - `pullrequest`, `pullrequest:write`
  - `pipeline`, `pipeline:write`
  - `runner`, `runner:write`
- Cannot be configured as a user with merge access in branch restriction rules — important limitation.
- Any content created by the token persists after revocation.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/intro/#access-tokens
Source: https://support.atlassian.com/bitbucket-cloud/docs/repository-access-tokens/

### 1.5 OAuth 2.0 Bearer Tokens

- As of **May 4th, 2026**, all OAuth 2.0 authenticated API requests must go to
  `https://api.bitbucket.org` with the access token as a Bearer header per RFC-6750:
  ```
  Authorization: Bearer {access_token}
  ```
- Access tokens expire in **1 hour**. Use refresh tokens to renew without user interaction.
- Refresh tokens expire after **3 months** if unused.
- For git clone/push over HTTPS: `https://x-token-auth:{access_token}@bitbucket.org/user/repo.git`
  (Note: literal string `x-token-auth` as username, unlike GitHub.)

Source: https://developer.atlassian.com/cloud/bitbucket/rest/intro/#oauth-2-0

### 1.6 Required Scopes Per Operation

For OAuth 2.0 / API token / access token use, required scope names are identical:

| Operation | OAuth 2.0 scope | Forge/API Token scope |
|-----------|----------------|----------------------|
| Read PRs, diff, activity | `pullrequest` | `read:pullrequest:bitbucket` |
| Create PR, post comment, approve, merge | `pullrequest:write` | `write:pullrequest:bitbucket` |
| Request changes, unapprove | `pullrequest:write` | `write:pullrequest:bitbucket` |
| Read repo/branch info | `repository` | `read:repository:bitbucket` |
| Read commit statuses | `repository` | `read:repository:bitbucket` |

Source: Each endpoint lists its scope requirements in the API docs at
https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/

---

## 2. Endpoints

All paths are relative to `https://api.bitbucket.org/2.0`.

### 2.1 Create Pull Request

```
POST /repositories/{workspace}/{repo_slug}/pullrequests
Content-Type: application/json
Scope: pullrequest:write
```

Minimum required body:
```json
{
  "title": "My Title",
  "source": {
    "branch": { "name": "my-feature-branch" }
  }
}
```

Optional fields:
```json
{
  "title": "...",
  "description": "...",
  "source": { "branch": { "name": "feature" } },
  "destination": { "branch": { "name": "main" } },
  "reviewers": [{ "uuid": "{504c3b62-8120-4f0c-a7bc-87800b9d6f70}" }],
  "close_source_branch": true,
  "draft": false
}
```

- If `destination` is omitted, defaults to `repository.mainbranch`.
- `reviewers` uses `uuid` (not username — usernames deprecated since April 2019).
- Response: `201 Created` with the full PR object including `id`, `links`, `participants`.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-post

### 2.2 List PR Comments

```
GET /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/comments
Scope: pullrequest
```

Returns paginated list of comments. Inline comments include the `inline` field.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-comments-get

### 2.3 Post PR Comment (General + Inline)

```
POST /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/comments
Content-Type: application/json
Scope: pullrequest:write
```

**General comment body:**
```json
{
  "content": { "raw": "Review comment text here", "markup": "markdown" }
}
```

**Inline comment body** (anchored to a diff hunk):
```json
{
  "content": { "raw": "Inline review text", "markup": "markdown" },
  "inline": {
    "path": "src/foo/bar.spl",
    "from": null,
    "to": 42
  }
}
```

- `from` and `to` are line numbers in the diff. `to` = destination file line. `from` can be null for additions-only anchors.
- Additional fields `start_from` and `start_to` available for range anchors.
- Response: `201 Created` with the comment object including `id`.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-comments-post

### 2.4 Reply to PR Comment

```
POST /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/comments
Content-Type: application/json
Scope: pullrequest:write
```

Body includes a `parent` object with the parent comment's `id`:
```json
{
  "content": { "raw": "Reply text", "markup": "markdown" },
  "parent": { "id": 12345 }
}
```

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-comments-post

### 2.5 Approve PR

```
POST /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/approve
Scope: pullrequest:write
```

No body required. Response `200 OK`:
```json
{
  "type": "participant",
  "role": "PARTICIPANT",
  "approved": true,
  "state": "approved",
  "participated_on": "..."
}
```

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-approve-post

### 2.6 Unapprove PR

```
DELETE /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/approve
Scope: pullrequest:write
```

Removes the authenticated user's approval. No body.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-approve-delete

### 2.7 Request Changes

```
POST /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/request-changes
Scope: pullrequest:write
```

GA endpoint — confirmed available in April 2026 docs. No body required. Response is the
`Participant` object with `state: "changes_requested"`.

Remove request-changes:
```
DELETE /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/request-changes
Scope: pullrequest:write
```

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-request-changes-post

### 2.8 Merge PR

```
POST /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/merge
Content-Type: application/json
Scope: pullrequest:write
```

Body:
```json
{
  "type": "pullrequest",
  "message": "Merge commit message",
  "close_source_branch": true,
  "merge_strategy": "merge_commit"
}
```

`merge_strategy` values: `"merge_commit"` | `"squash"` | `"fast_forward"`.
The available strategies depend on repository settings (`merge_strategies` array in PR object,
`default_merge_strategy` field).

Response: `200 OK` with the merged PR object. `202 Accepted` if the merge is async (large
repos). `409 Conflict` if the PR is not mergeable.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-merge-post

### 2.9 Get PR Diff

```
GET /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/diff
Scope: pullrequest
```

Returns `302 Moved Temporarily` redirect to the repository diff endpoint with the correct
revspec. Follow the redirect to get the unified diff content (text/x-patch).

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-diff-get

### 2.10 Get PR Diffstat

```
GET /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/diffstat
Scope: pullrequest  (Forge: read:pullrequest:bitbucket)
```

Returns `302` redirect to the repository diffstat endpoint. The diffstat lists files changed,
lines added/removed. Useful for determining if a PR has no actual code changes.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-diffstat-get

### 2.11 List PR Activity

```
GET /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/activity
Scope: pullrequest
```

Returns paginated activity log including approval events, comment events, update events.
Approval entries in the response look like:
```json
{
  "approval": {
    "date": "2019-09-27T00:37:19...",
    "pullrequest": { ... },
    "user": { ... }
  }
}
```

Also available without a specific PR ID to get activity across all PRs:
```
GET /repositories/{workspace}/{repo_slug}/pullrequests/activity
```

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-activity-get

### 2.12 List PR Commit Statuses (Build Checks)

```
GET /repositories/{workspace}/{repo_slug}/commit/{commit}/statuses
Scope: repository
```

Also available as a redirect from the PR:
```
GET /repositories/{workspace}/{repo_slug}/pullrequests/{pull_request_id}/statuses
Scope: pullrequest
```

Each status has:
- `state`: `"SUCCESSFUL"` | `"FAILED"` | `"INPROGRESS"` | `"STOPPED"`
- `key`: CI system identifier
- `name`, `url`, `description`

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-commit-statuses/

---

## 3. Rate Limits

**Important:** The dedicated rate limits page (`/cloud/bitbucket/rate-limits/`) returned 404
as of April 2026 — Atlassian has removed or moved it. The following is based on documented
behavior in the API intro and practical community knowledge:

- The `developer.atlassian.com` rate limits page no longer resolves. Atlassian may have folded
  rate limit documentation into individual endpoint pages or removed explicit numbers.
- Bitbucket Cloud historically applied a limit of **1,000 API requests per hour** per
  authenticated user/token. This figure is not currently confirmed in live docs (page 404).
- OAuth 2.0 access tokens expire in **1 hour** — the auth refresh loop and polling loop must
  be designed to handle token refresh independently of rate limit windows.
- **Poll-merge loop recommendation:** With an unknown confirmed limit, use exponential backoff
  starting at 30s intervals. Poll at most once every 30–60 seconds. At 60s intervals, a 1-hour
  poll window = 60 requests, well within any reasonable limit.
- For Bitbucket Pipelines (CI), there is explicit rate-limit documentation per third-party
  provider, but REST API limits for external callers are currently undocumented at the URL
  provided.

**Free tier access:** The free tier supports up to 5 users. The REST API (PR, comments,
approve, merge) is fully accessible on free tier — no feature gating observed in docs. Build
minutes (Pipelines) are limited to 50/month on free tier, but external CI via commit statuses
is unlimited.

Source: https://www.atlassian.com/software/bitbucket/pricing (plan comparison)
Source: https://developer.atlassian.com/cloud/bitbucket/rest/intro/ (no rate limit numbers stated)

---

## 4. Detecting "All Required Reviewers Approved + All Checks Passing"

### 4.1 Check Required Reviewers Approved

The PR object returned by `GET /repositories/{workspace}/{repo_slug}/pullrequests/{id}`
includes a `participants` array. Each participant has:
```json
{
  "role": "REVIEWER",
  "approved": true,
  "state": "approved"
}
```

To check if all required reviewers approved:
1. Call `GET /repositories/{workspace}/{repo_slug}/pullrequests/{id}` — check `participants`
   where `role == "REVIEWER"` and verify all have `approved == true`.
2. Alternatively, check PR `state` field — a PR is mergeable when its `state` is `"OPEN"` and
   all branch restrictions pass. Attempting `merge` will return `409` if not mergeable.

**Note on branch restrictions:** The "required reviewers" merge check is configurable via
branch restrictions (`/repositories/{workspace}/{repo_slug}/branch-restrictions`). On the free
tier, basic branch permissions exist but "required reviewers" as an enforced merge check may
require Standard/Premium plan. Verify per workspace before relying on it programmatically.
The bot can still check `participants[].approved` itself as a pre-flight regardless of plan.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/#api-repositories-workspace-repo-slug-pullrequests-pull-request-id-get
Source: https://developer.atlassian.com/cloud/bitbucket/rest/api-group-branch-restrictions/

### 4.2 Check All CI Statuses Passing

```
GET /repositories/{workspace}/{repo_slug}/pullrequests/{id}/statuses
```

Iterate response, check all `state == "SUCCESSFUL"` and none `"FAILED"` or `"INPROGRESS"`.

### 4.3 Pre-merge Check Strategy

```
1. GET PR → check state == "OPEN"
2. GET PR → check all participants[role=REVIEWER].approved == true
3. GET statuses → check all state == "SUCCESSFUL"
4. POST merge → handle 409 as "not ready", retry after backoff
```

---

## 5. Webhook Event Names (for Future Push-Mode)

To replace polling with webhooks, register at:
```
POST /repositories/{workspace}/{repo_slug}/hooks
```

Relevant event keys for the PR pipeline:

| Event key | Trigger |
|-----------|---------|
| `pullrequest:created` | PR opened |
| `pullrequest:updated` | PR title/description/reviewers changed |
| `pullrequest:approved` | A reviewer approves |
| `pullrequest:unapproved` | Approval removed |
| `pullrequest:changes_request_created` | Changes requested |
| `pullrequest:changes_request_removed` | Changes request removed |
| `pullrequest:fulfilled` | PR merged (fulfilled = merged) |
| `pullrequest:rejected` | PR declined |
| `pullrequest:comment_created` | New comment posted |
| `pullrequest:comment_updated` | Comment edited |
| `pullrequest:comment_deleted` | Comment deleted |
| `pullrequest:comment_resolved` | Comment thread resolved |
| `pullrequest:comment_reopened` | Comment thread reopened |

Webhook payloads include `actor`, `pullrequest`, and `repository` objects.
All webhook endpoints must use HTTPS with a valid public CA certificate.

Source: https://support.atlassian.com/bitbucket-cloud/docs/event-payloads/

---

## 6. Bitbucket Cloud vs Bitbucket Server/DC — Key Differences

We are targeting **Bitbucket Cloud only**. Gotchas when reading docs:

| Topic | Cloud (target) | Server/DC (NOT target) |
|-------|---------------|------------------------|
| Base URL | `api.bitbucket.org/2.0` | `{host}/rest/api/1.0` — completely different |
| Auth | API Tokens, Access Tokens, OAuth 2.0 | Personal Access Tokens, HTTP Basic |
| Inline comment body | `inline: { path, from, to, start_from, start_to }` | Different field names |
| PR approval | `/pullrequests/{id}/approve` | `/pullrequests/{id}/participants/{userSlug}` with `PUT` |
| Webhook events | `pullrequest:fulfilled` for merged | `pr:merged` in DC |
| Rate limits | Per-user, cloud-managed | Per-instance, admin-configured |
| API version | REST API 2.0 | REST API 1.0 (completely separate) |

Do **not** mix Cloud and Server docs. The Atlassian developer site has a "Cloud / Data Center"
toggle — always verify Cloud is selected.

Source: https://developer.atlassian.com/cloud/bitbucket/rest/intro/ (note "Cloud" tab)

---

## 7. Decisions for Adapter

### Auth: Use Repository Access Token (not API Token, not App Password, not OAuth 2.0)

**Recommendation: Repository Access Token with Bearer header.**

Rationale:
1. **App Passwords are deprecated** (confirmed April 2026) — do not use.
2. **API Tokens** are per-user and tied to an individual's Atlassian account. For a bot, this means
   coupling the bot to a human account, which is fragile (account deletion, 2FA changes, etc.).
3. **Repository Access Tokens** are machine-scoped, created by an admin, use Bearer auth (no
   user email needed), and have exactly the scopes we need (`pullrequest:write`). They are the
   correct choice for CI/bot automation.
4. **OAuth 2.0** requires user interaction for the authorization_code flow and token refresh
   complexity — not suitable for unattended bot.
5. **Workspace Access Tokens** are an acceptable alternative if the bot needs to operate across
   multiple repos in the workspace. Prefer repo-scoped for principle of least privilege.

**Header format:**
```
Authorization: Bearer {token}
```

**Required scopes:** `pullrequest:write` (covers all PR operations including read, comment,
approve, merge) and `repository` (for commit statuses).

### Poll-Merge Loop

Use 60-second polling intervals with exponential backoff on 429 responses. Do not exceed
~30 calls/hour per PR to stay conservative (official rate limit is undocumented after the
page 404'd).

### Merge Strategy

Default to `"merge_commit"` (always available). Allow override via config for `"squash"` or
`"fast_forward"`. Check the PR's `merge_strategies` array to validate the configured strategy
is supported by the repo before attempting merge.

### Inline Comments

Use `inline: { path, to: <line_number> }` for line comments on the destination file. Set
`from` to the corresponding source line for changed-line anchors, or `null` for addition-only
lines.

### Detecting Merge Readiness

Poll `GET /pullrequests/{id}` + `GET /pullrequests/{id}/statuses`. Do not rely solely on
branch restrictions — check `participants[role=REVIEWER].approved` directly in the adapter.
Treat a `409` from the merge endpoint as a "not yet ready" signal rather than a fatal error.

### Webhook Future-Proofing

Design the adapter so `poll_until_merged()` is a pluggable strategy. When webhooks are added
later, replace the poll loop with a `pullrequest:fulfilled` / `pullrequest:approved` receiver.
The endpoint shape is identical — only the trigger mechanism changes.

### Free Tier Blockers

**No blockers for the core Level 2/3 pipeline on free tier.** All required REST API endpoints
are accessible. Potential limitation: enforced "required reviewers" branch merge checks may
require Standard/Premium plan — but the bot can implement the same check itself via the
participants array regardless of plan enforcement.
