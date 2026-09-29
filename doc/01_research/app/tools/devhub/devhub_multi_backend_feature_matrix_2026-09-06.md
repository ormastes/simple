# devhub multi-backend research: features, backends, and from→to field maps

**Date:** 2026-09-06
**Supersedes nothing; extends** `devhub_cli_wrapper_forwarding_2026-09-06.md`, which
organised the problem *by area* and shipped the `gh` shim. This document
re-organises **by feature**, decides **which backends to support**, and gives the
**field-level from→to mapping tables** needed to add them.

---

## 0. Method, and its limits

Field names below were checked against vendor documentation via web search on
2026-09-06 (sources listed per section), and cross-checked against devhub's
existing adapters where one exists. Two honest caveats:

- **The repo's own sanctioned fetch tool cannot read any of these docs.**
  `simple_ctx_fetch_and_index` fails with `native HTTP supports http:// only;
  HTTPS requires the TLS runtime`, and `curl`/`wget`/`WebFetch` are blocked by
  project hooks. Every API reference worth reading is HTTPS. This is a real gap
  in the research toolchain, filed in §9.
- Rows marked **(unverified)** come from working knowledge and were not
  confirmed against a live response this session. They are the ones to check
  first when implementing that backend.

---

## 1. The organising idea: feature, not product

The earlier research grouped by *area* ("git hosting", "storage"), which maps
cleanly onto vendors but badly onto code. A vendor is not a unit of work — a
**feature** is. Bitbucket and Jira are one vendor and two features; GitHub is
one vendor and six features.

Reorganising by feature makes three things fall out that were invisible before:

1. **A backend is a (feature, vendor) pair, not a vendor.** "Support GitLab" is
   not one task: GitLab offers merge requests, issues, a wiki, a registry and
   CI, and devhub could adopt any subset. The unit of support is
   `issues@gitlab`, not `gitlab`.
2. **The canonical shape is per-feature.** PRs speak `gh`; objects speak `mc`;
   mail speaks Gmail. A single "devhub object model" would be wrong for all
   three.
3. **Capability gaps are per-(feature, vendor) cells**, so they belong in a
   table, not in hand-written refusal lists. This is what today's code gets
   wrong — see §8.

---

## 2. Feature inventory, and what devhub has today

| # | Feature | Canonical shape (what the LLM sees) | devhub facade | Backends today |
|---|---|---|---|---|
| F1 | **Pull / merge requests** | `gh pr` | `gh`/`git` | github, bitbucket |
| F2 | **Issues / work items** | `gh issue` | `tasks` | github, jira |
| F3 | **Repositories** | `gh repo` | `gh`/`git` | github, bitbucket |
| F4 | **Review comments** | `gh pr comment/review` | `gh`/`git` | github, bitbucket |
| F5 | **CI runs / checks** | `gh run`, `gh pr checks` | — | **none** |
| F6 | **Releases / artifacts** | `gh release` | — | **none** |
| F7 | **Wiki / pages** | gh-flavoured (`list/view/edit`) | `wiki` | confluence, github-wiki |
| F8 | **Object storage** | `mc` / `aws s3` | `storage` | minio/S3 |
| F9 | **Email** | Gmail vocabulary | `email` | gmail(IMAP), outlook(Graph), imap |
| F10 | **Secrets / variables** | `gh secret` | — | **none** |

**F5, F6 and F10 have no facade at all.** F5 is the notable hole: `gh pr checks`
is how an agent decides whether a PR is mergeable, and this repo's own workflow
depends on exactly that (see the PR-merge waiting in `vcs.md`).

---

## 3. Which backends to support

Ranked by *coverage per unit of work*, not by popularity. The costly axis is
almost never the HTTP client — it is the **shape distance** from the canonical
model (§5) and the **auth model** (§7).

### Tier 1 — adopt

| Backend | Features | Why | Cost |
|---|---|---|---|
| **GitLab** (SaaS + self-managed) | F1–F7 | The single largest coverage gain per backend: one REST API, one token, and six features land at once. `glab` already clones `gh`'s grammar, so the CLI surface is a rename table. | **Low–medium.** Shape distance is small; the `iid`-vs-`id` trap (§5.1) is the only sharp edge. |
| **Gitea / Forgejo** | F1–F4, F6 | Its API is deliberately GitHub-shaped — `number`, `head.ref`, `base.ref`, `html_url` are near-identical, so the mapping is close to the identity function. Cheapest backend to add, and it covers self-hosted teams. | **Low.** |

### Tier 2 — adopt when a user needs it

| Backend | Features | Why | Cost |
|---|---|---|---|
| **Azure DevOps** | F1–F6 | Common in enterprises, and the only one covering both repos and boards. | **Medium–high.** Fully-qualified ref names, a different id vocabulary, and work-item fields addressed as `System.*` strings (§5.2). |
| **Bitbucket Data Center** (self-hosted) | F1–F4 | A *different* API from Bitbucket Cloud (`/rest/api/1.0`, not `/2.0`), so today's Cloud adapter does **not** work against it. | **Medium.** New adapter, familiar domain. |
| **Linear** | F2 | Fast-growing tracker; GraphQL-only. | **Medium.** GraphQL client, and string identifiers (§5.2). |
| **S3-compatible (R2, B2, GCS, Azure Blob)** | F8 | R2/B2 are drop-in for the existing SigV4 adapter; GCS and Azure Blob are not. | **R2/B2 low; GCS/Azure medium** (different auth). |

### Tier 3 — decline, with reasons

| Backend | Why not |
|---|---|
| **Gerrit** | Change-centric, not PR-centric: a change is a *patchset series* with no branch pair. Mapping it onto `gh pr` would misrepresent the model rather than translate it. |
| **Notion (as wiki)** | Pages are a **block tree**, not a document. Round-tripping through markdown is lossy in both directions; devhub would silently destroy content on edit. Read-only support would be defensible; read-write is not. |
| **MediaWiki** | Wikitext ≠ markdown, and no team in scope uses it. |
| **JMAP** | Correct design, near-zero deployment. Revisit if Fastmail-class hosts matter. |

**Recommendation:** GitLab then Gitea. Those two take F1–F7 from "GitHub or
Bitbucket" to "four hosting vendors" while adding one REST client each.

---

## 4. Canonical models (the "to" side)

Everything maps *to* these. They are gh/mc/Gmail's own field names, not invented.

```
PullRequest  number, title, state, url, headRefName, baseRefName,
             author.login, body, isDraft, createdAt, updatedAt, mergedAt
Issue        number, title, state, url, author.login, body,
             labels[], assignees[].login, createdAt, updatedAt, closedAt
Page         title, path, body, url, updatedAt
Object       key, size, lastModified, etag, storageClass
Message      id, threadId, from, to, subject, snippet, labels[], date, unread
```

---

## 5. From → to mapping tables

### 5.1 F1 — Pull / merge requests

| canonical (`gh`) | GitHub | GitLab | Bitbucket Cloud | Gitea / Forgejo | Azure DevOps |
|---|---|---|---|---|---|
| `number` | `number` | **`iid`** ⚠ | `id` | `number` | `pullRequestId` |
| `title` | `title` | `title` | `title` | `title` | `title` |
| `state` | `state` | `state` ⚠ `opened` | `state` ⚠ `DECLINED` | `state` + `merged` | `status` ⚠ `active/completed/abandoned` |
| `url` | `url` | `web_url` | `links.html.href` | `html_url` | *(construct)* ⚠ |
| `headRefName` | `headRefName` | `source_branch` | `source.branch.name` | `head.ref` | `sourceRefName` ⚠ `refs/heads/…` |
| `baseRefName` | `baseRefName` | `target_branch` | `destination.branch.name` | `base.ref` | `targetRefName` ⚠ `refs/heads/…` |
| `author.login` | `author.login` | `author.username` | `author.nickname` | `user.login` | `createdBy.uniqueName` |
| `body` | `body` | `description` | `description` | `body` | `description` |
| `isDraft` | `isDraft` | `draft` | **absent** ⚠ | `draft` | `isDraft` |
| `createdAt` | `createdAt` | `created_at` | `created_on` | `created_at` | `creationDate` |
| `mergedAt` | `mergedAt` | `merged_at` | *(state=MERGED)* ⚠ | `merged_at` | `closedDate` + status |

**Four traps that will bite whoever implements these:**

1. **GitLab `iid` vs `id`.** `id` is globally unique across the instance; `iid`
   is the per-project number a human sees and every URL uses. Reading `id` and
   calling it `number` produces valid-looking output that links nowhere and
   cannot be looked up. This is *the* GitLab integration bug.
2. **Azure fully-qualified refs.** `sourceRefName` is `refs/heads/topic`, not
   `topic`. Passing it back to `gh`-shaped tooling as `headRefName` yields a
   branch name nothing matches.
3. **State vocabularies do not align three ways.** gh has `OPEN/CLOSED/MERGED`;
   GitLab says `opened`; Bitbucket splits closed into `DECLINED` *and*
   `SUPERSEDED`; Azure calls them `active/abandoned/completed`. Every direction
   needs an explicit table — never a `.upper()`.
4. **Draft PRs do not exist on Bitbucket Cloud.** Emit `isDraft: false`
   (devhub already does) and refuse `--draft` on input (devhub already does).

Sources: [GitLab MR API](https://docs.gitlab.com/api/merge_requests/),
[Gitea API](https://docs.gitea.com/api/next/),
[Azure DevOps PR API](https://learn.microsoft.com/en-us/rest/api/azure/devops/git/pull-requests/get-pull-requests?view=azure-devops-rest-7.1).

### 5.2 F2 — Issues / work items

| canonical (`gh issue`) | GitHub | GitLab | Jira | Linear | Azure Boards |
|---|---|---|---|---|---|
| `number` | `number` (int) | `iid` (int) | **`key`** ⚠ `"PROJ-123"` | **`identifier`** ⚠ `"ENG-42"` | `id` (int) |
| `title` | `title` | `title` | `fields.summary` | `title` | `fields."System.Title"` |
| `state` | `state` | `state` | `fields.status.name` (+ `statusCategory`) ⚠ | `state.name` (+ `state.type`) | `fields."System.State"` |
| `body` | `body` | `description` | `fields.description` ⚠ **ADF object** | `description` (markdown) | `fields."System.Description"` ⚠ HTML |
| `author.login` | `author.login` | `author.username` | `fields.reporter.displayName` | `creator.name` | `System.CreatedBy` |
| `assignees[]` | `assignees[].login` | `assignees[].username` | `fields.assignee` ⚠ **one only** | `assignee` ⚠ **one only** | `System.AssignedTo` ⚠ **one only** |
| `labels[]` | `labels[].name` | `labels[]` | `fields.labels[]` | `labels.nodes[].name` | `System.Tags` ⚠ **`"a; b"` string** |
| `url` | `url` | `web_url` | *(construct `…/browse/KEY`)* | `url` | `_links.html.href` |

**Traps:**

1. **`number` is not a number.** Jira (`PROJ-123`) and Linear (`ENG-42`) use
   string identifiers. A canonical model typed `number: int` cannot represent
   them. devhub already dodges this by auto-detecting the `PROJ-123` shape, but
   any typed model added later must make this field **text**.
2. **Jira descriptions are ADF, and the conversion is one-way today.** Jira
   Cloud REST **v3 does not accept plain text**, and **v2 does not accept
   ADF** — they are not interchangeable. devhub targets v3
   (`auth.spl` → `rest/api/3`) and correctly wraps outbound plain text with
   `_adf_doc`. **The inbound direction is missing** — see §9.1.
3. **One assignee, not many.** Jira, Linear and Azure each allow exactly one.
   `gh issue --add-assignee` twice must fail loudly, not silently keep the last.
4. **Azure tags are a delimited string**, not an array.

Sources: [Jira ADF](https://developer.atlassian.com/cloud/jira/platform/apis/document/structure/),
[Jira v3 intro](https://developer.atlassian.com/cloud/jira/platform/rest/v3/intro/),
[Linear GraphQL](https://linear.app/developers/graphql).

### 5.3 F7 — Wiki / pages

| canonical | Confluence | GitHub wiki | GitLab wiki | Notion *(declined)* |
|---|---|---|---|---|
| `title` | `title` | filename stem | `title` | `properties.title` |
| `body` | `body.storage.value` ⚠ **XHTML** | file bytes (markdown) | `content` | block tree ⚠ |
| `path` | ancestor chain | file path in `.wiki.git` | `slug` | page id |
| `url` | `_links.webui` | `html_url` | `web_url` | `url` |
| `updatedAt` | `version.createdAt` | git commit date | *(absent)* | `last_edited_time` |

**Trap:** Confluence's storage format is **XHTML with Atlassian macros**, not
markdown. devhub has `convert_storage.spl` for this; any new wiki backend needs
its own converter, and lossiness must be stated rather than hidden.

### 5.4 F8 — Object storage

| canonical (`mc`) | S3 / MinIO | GCS | Azure Blob | Cloudflare R2 | Backblaze B2 |
|---|---|---|---|---|---|
| `key` | `Key` | `name` | `Name` | `Key` | `fileName` |
| `size` | `Size` (int) | `size` ⚠ **string** | `Content-Length` | `Size` | `contentLength` |
| `lastModified` | `LastModified` | `updated` | `Last-Modified` | `LastModified` | `uploadTimestamp` ⚠ **epoch ms** |
| `etag` | `ETag` | `etag` | `Etag` | `ETag` | `contentSha1` |

**Trap:** R2 and B2's S3 endpoint work with the **existing SigV4 adapter** — they
are configuration, not code. GCS and Azure Blob are **not** SigV4 and need new
signing. That difference is the whole cost story for F8.

### 5.5 F9 — Email

| canonical (Gmail) | Gmail API | MS Graph | IMAP | JMAP *(declined)* |
|---|---|---|---|---|
| `id` | `id` | `id` | `UID` | `id` |
| `threadId` | `threadId` | `conversationId` | *(derive from `References`)* ⚠ | `threadId` |
| `from` | header `From` | `from.emailAddress.address` | header `From` | `from[].email` |
| `subject` | header `Subject` | `subject` | header `Subject` | `subject` |
| `unread` | label `UNREAD` | `isRead` ⚠ **inverted** | `\Seen` ⚠ **inverted** | `keywords.$seen` ⚠ **inverted** |
| `labels[]` | `labelIds` | `categories` + folder | flags + folder | `mailboxIds` |

**Trap:** three of four backends express **read**, Gmail expresses **unread**.
Every one of them is an inversion, and getting it backwards marks the whole
inbox read. This is the single most common mail-integration bug.

---

## 6. Capability matrix (drives refusals)

`✓` supported · `—` absent in the backend · `~` partial

| Capability | GitHub | GitLab | Bitbucket Cloud | Gitea | Azure | Jira | Linear |
|---|---|---|---|---|---|---|---|
| Draft PR | ✓ | ✓ | — | ✓ | ✓ | n/a | n/a |
| Auto-merge | ✓ | ✓ | — | ~ | ✓ | n/a | n/a |
| Rebase merge | ✓ | ✓ | ~ `fast_forward` | ✓ | ✓ | n/a | n/a |
| Request changes | ✓ | ✓ | — | ✓ | ✓ | n/a | n/a |
| Multiple assignees | ✓ | ✓ | ~ reviewers | ✓ | — | — | — |
| Free-text search | ✓ | ✓ | — | ~ | ✓ | ✓ JQL | ✓ |
| Labels | ✓ | ✓ | — | ✓ | ~ tags | ✓ | ✓ |
| Merge-queue | ✓ | ✓ trains | — | — | — | n/a | n/a |

**This table is the specification for the refusal logic.** Today those refusals
are hand-written lists in `gh_compat.spl`; §8 proposes deriving them from here.

---

## 7. Auth models

| Backend | Mechanism | Devhub fit |
|---|---|---|
| GitHub | `gh auth` / PAT / GitHub App | delegated to `gh` today |
| GitLab | PAT or project token, `PRIVATE-TOKEN` header | fits `token_env` as-is |
| Bitbucket Cloud | Repository Access Token, `Bearer` | implemented |
| Gitea | PAT, `Authorization: token …` | fits as-is |
| Azure DevOps | PAT via **Basic**, empty username ⚠ | needs a Basic variant |
| Jira / Confluence | Basic `email:token` | implemented |
| Linear | `Authorization: <key>` ⚠ **no `Bearer` prefix** | fits, with a note |
| S3 / R2 / B2 | SigV4 | implemented |
| GCS / Azure Blob | OAuth2 / SharedKey | new signing |

Every one of these is a *token* — so the credential mechanism landed in the
previous change (`[token_env]` naming an environment variable, `[token_cmd]`
running a command, both resolved by `resolve_auth_token`) already covers Tier 1
and Tier 2 without modification. **Auth is not the blocker for any Tier-1
backend.**

---

## 8. How to support many backends structurally

Today, adding a backend means editing at least five places:
`normalize_backend`'s match arms, the per-verb `*_KNOWN` allowlists, the
`first_unsupported_flag` refuse-lists, `gh_pr_to_bb_argv`'s hardcoded
Bitbucket renames, and `cmd_git.spl`'s `match backend:`. Every one is a
`bitbucket`-shaped hole. Three backends in, that is unmaintainable and
guarantees the lists drift apart — which is exactly the class of bug that
produced the `--body-file` and `--json` defects in the previous change.

**Proposal: a declarative backend registry.**

```
BackendSpec
  id, aliases[], features[]           # which of F1..F10 it serves
  capabilities: Dict<text, bool>      # §6, verbatim
  field_map:   Dict<text, text>       # canonical -> backend path ("source.branch.name")
  state_map:   Dict<text, text>       # canonical <-> backend vocabulary
  flag_map:    Dict<text, text>       # gh flag -> backend flag
  auth: {kind, header, token_env}
```

Then:

- `normalize_backend` becomes a lookup over `aliases`.
- The refusal check becomes *"is this canonical capability true for this
  backend"*, so a flag with no cell is refused **by construction** — the
  property the allowlist fix bought manually, now free for every backend.
- `bb_pr_object_to_gh` becomes one generic walker over `field_map`, replacing
  one hand-written function per backend.
- Adding Gitea becomes a table entry plus an auth row.

**Staging.** Do not refactor and add a backend in the same change: land the
registry with `github`/`bitbucket` re-expressed in it and the existing specs
still green (pure refactor, behaviour-preserving), *then* add GitLab as the
first table-only backend. If GitLab lands before the registry, it will be a
third hardcoded branch and the registry gets harder, not easier.

---

## 9. Concrete defects found while doing this research

### 9.1 Jira descriptions are written as ADF but read as raw JSON — devhub, live

`adapter_jira_curl.spl` has `_adf_doc` (`:251`) and correctly wraps outbound
plain text into an ADF document for REST v3. The **inbound** path does not
invert it: `_jstr(source, "description")` (`:216`, via `:196`) JSON-serialises
the value and strips surrounding quotes — but an ADF description is a JSON
**object**, so the serialised form does not start with `"` and is returned
whole. `devhub tasks view PROJ-123` therefore renders the description as a raw
`{"type":"doc","version":1,…}` blob instead of text.

This is precisely the outbound half of the goal's question 3 ("backend out like
most famous platform") going unimplemented for one field. Fix: an
`_adf_to_plain` walker (concatenate `content[].content[].text` across
paragraph nodes) applied wherever `description` is read. Cheap, and testable
offline with a fixture.

### 9.2 The sanctioned research tool cannot read HTTPS

`simple_ctx_fetch_and_index` — the tool `CLAUDE.md` mandates instead of
`curl`/`WebFetch` — fails on every `https://` URL with `native HTTP supports
http:// only; HTTPS requires the TLS runtime`. Since `curl`, `wget`, inline
HTTP and `WebFetch` are all hook-blocked, **there is currently no working path
from this repo to any vendor API documentation**, which is why §0 has to flag
unverified rows. Either the MCP fetch tool needs the TLS runtime linked, or the
hook needs an escape for documentation fetches.

### 9.3 Bitbucket Data Center is not Bitbucket Cloud

`adapter_bitbucket.spl` hardcodes the Cloud REST **2.0** shape
(`/2.0/repositories/{ws}/{repo}/pullrequests`, `values[]` pagination). Bitbucket
Server / Data Center uses `/rest/api/1.0/projects/{key}/repos/{slug}/pull-requests`
with a different response envelope. A self-hosted user pointing devhub at their
server gets 404s, and nothing in the config or the error text says why. At
minimum the `bitbucket` backend should be documented as Cloud-only; better, it
should be two backend ids (`bitbucket`, `bitbucket-dc`).

---

## 10. Recommended order of work

| Step | Work | Why first |
|---|---|---|
| 1 | Fix §9.1 (ADF read) | Live defect, one function, offline-testable |
| 2 | Land the registry (§8) with github+bitbucket only | Behaviour-preserving; makes 3+ backends tractable |
| 3 | Add **GitLab** F1/F3 (MRs, repos) | Largest coverage gain; `iid` trap known |
| 4 | Add **Gitea** F1/F3 | Nearly the identity mapping once the registry exists |
| 5 | Add F5 (`gh pr checks`) for github+gitlab | The missing feature this repo's own workflow needs |
| 6 | Rename `bitbucket` → `bitbucket-cloud`, document §9.3 | Honesty about what is supported |

Deliberately not scheduled: Azure DevOps, Linear, GCS/Azure Blob (Tier 2, on
demand), and everything in Tier 3.

---

## Sources

- [GitLab Merge requests API](https://docs.gitlab.com/api/merge_requests/)
- [Gitea API documentation](https://docs.gitea.com/api/next/)
- [Azure DevOps Git Pull Requests REST API](https://learn.microsoft.com/en-us/rest/api/azure/devops/git/pull-requests/get-pull-requests?view=azure-devops-rest-7.1)
- [Atlassian Document Format](https://developer.atlassian.com/cloud/jira/platform/apis/document/structure/)
- [Jira Cloud REST API v3 intro](https://developer.atlassian.com/cloud/jira/platform/rest/v3/intro/)
- [Jira Cloud REST API v2 intro](https://developer.atlassian.com/cloud/jira/platform/rest/v2/intro/)
- [Linear GraphQL API](https://linear.app/developers/graphql)
