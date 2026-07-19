<!-- codex-research -->
# LLM Caret + SPipe infrastructure access hardening: domain research

Date: 2026-07-18

## Scope and method

This research compares current official interfaces for repository hosting, task
management, object storage, mail, and wikis. "Canonical" below means the most
useful de-facto compatibility contract for developer tooling; it is not a
market-share claim. A sidecar collected the broad provider matrix and the
primary model reviewed the recommendations against official documentation.

## Recommended compatibility surfaces

### Repository hosting: GitHub CLI (`gh`)

Use the `gh` command shape for repository, pull-request, issue, release,
workflow, run, authentication, and raw API operations. Preserve `--repo`,
`--json`, `--jq`, stdin/body-file input, exit status, and pagination behavior.
Bitbucket pull requests and GitLab merge requests can map into that surface,
but provider-specific fields and unsupported GitHub GraphQL/Actions operations
must produce explicit capability errors rather than fabricated results.

Sources: [GitHub CLI manual](https://cli.github.com/manual/gh),
[pull requests](https://cli.github.com/manual/gh_pr),
[raw API and pagination](https://cli.github.com/manual/gh_api),
[Bitbucket pull-request REST API](https://developer.atlassian.com/cloud/bitbucket/rest/api-group-pullrequests/).

### Task management: Atlassian CLI (`acli jira`)

Use `acli jira` as the broad task/project model because it covers work items,
projects, boards, sprints, filters, and dashboards. Offer a narrower
developer-issue profile compatible with `gh issue` for repository-bound work.
Map GitHub issue labels directly where possible; map milestones to Jira fix
versions or sprints only through configuration. JQL, workflow transitions,
permissions, boards, and custom fields are provider-native capabilities and
cannot be assumed lossless.

Sources: [ACLI Jira commands](https://developer.atlassian.com/cloud/acli/reference/commands/jira/),
[ACLI login](https://developer.atlassian.com/cloud/acli/reference/commands/jira-auth-login/),
[Jira REST v3](https://developer.atlassian.com/cloud/jira/platform/rest/v3/intro/),
[GitHub issue CLI](https://cli.github.com/manual/gh_issue).

### Object storage: AWS CLI S3

Use the high-level `aws s3` surface for `ls`, `cp`, `mv`, `rm`, and `sync`,
and the low-level `aws s3api` surface for service-specific operations. Preserve
`s3://` URIs, `--endpoint-url`, stdin/stdout `-`, streaming, multipart transfer,
metadata, ETags, and pagination controls. MinIO is an endpoint/credential/
addressing configuration of this contract, not a separate object model.

Normalize service errors to code, message, request ID, and HTTP status. Retry
only safe/idempotent operations and retryable throttling/5xx responses with a
bounded policy.

Sources: [AWS CLI S3](https://docs.aws.amazon.com/cli/latest/reference/s3/),
[AWS CLI pagination](https://docs.aws.amazon.com/cli/latest/userguide/cli-usage-pagination.html),
[MinIO client](https://min.io/docs/minio/linux/reference/minio-mc.html).

### Mail: Gmail REST resource model

There is no stable, universal mail CLI. Use Gmail REST resources as the common
semantic model: threads, messages, labels, drafts, attachments, history/watch,
and Gmail search. Treat any Google Workspace CLI syntax as provisional rather
than a compatibility promise.

The Microsoft Graph adapter maps folders/categories/conversations to the common
model only where semantics agree, and must preserve provider IDs and MIME.
Graph `@odata.nextLink`/delta links and Gmail `nextPageToken`/history IDs stay
opaque. A missing Gmail history range requires full resynchronization; Graph
and Gmail throttling must honor provider retry guidance.

Sources: [Gmail API guide](https://developers.google.com/workspace/gmail/api/guides),
[Gmail REST reference](https://developers.google.com/workspace/gmail/api/reference/rest),
[Microsoft Graph mail overview](https://learn.microsoft.com/en-us/graph/api/resources/mail-api-overview?view=graph-rest-1.0),
[Graph paging](https://learn.microsoft.com/en-us/graph/paging),
[Graph throttling](https://learn.microsoft.com/en-us/graph/throttling).

### Wiki: neutral page CLI with provider escape hatches

No de-facto universal official wiki CLI exists. `gh` has no wiki CRUD family;
GitHub Wiki automation uses git against `<repo>.wiki.git`. Confluence content
automation uses REST v2. Define only `wiki page list|get|create|update|delete`
plus search and a raw provider escape hatch.

The GitHub adapter maps pages to Markdown files and git commits. The Confluence
adapter preserves page ID, space, parent, body representation, and version.
HTML/storage-format to Markdown conversion is lossy, so retain the raw body or
reject destructive round-trips when fidelity cannot be proved.

Sources: [GitHub wiki git workflow](https://docs.github.com/en/communities/documenting-your-project-with-wikis/adding-or-editing-wiki-pages),
[Confluence REST v2](https://developer.atlassian.com/cloud/confluence/rest/v2/intro/),
[Confluence page API](https://developer.atlassian.com/cloud/confluence/rest/v2/api-group-page/).

## Cross-provider contract

- Secrets enter through stdin, keyring, or environment indirection, never argv
  or logs; scopes are least-privilege.
- Pagination cursors and provider IDs remain opaque.
- Machine output supports JSON and, for streams, NDJSON.
- Errors retain provider code, HTTP status, request ID, and retry metadata.
- Capability discovery distinguishes unsupported operations from failures.
- Retries are bounded, honor `Retry-After`, and avoid replaying unsafe writes.
- Large objects and attachments stream rather than buffer in memory.
- Conditional writes, versions, ETags, or idempotency keys protect mutations.

## Applied conclusion

Do not build one giant lowest-common-denominator API. Reuse a small set of
familiar command contracts, route them through typed provider capabilities, and
keep a provider-native escape hatch. This minimizes new surface while making
unsupported or lossy behavior visible.
