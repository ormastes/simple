# LLM Caret and SPipe Infrastructure Access Hardening

Status: selected design A + NFR 2; implementation evidence is tracked below.

Provenance: the initial guide draft was produced by the configured
`gpt-5.4-mini` smaller-model sidecar on 2026-07-18. The primary high-capability
model then reviewed it against the local and domain research, corrected
provider-identity and architecture-selection claims, and added the concrete
mapping and evidence tables below.

## Purpose

This guide records the implementation truth and selected compatibility rules
for connecting LLM Caret, SPipe, and infrastructure access. It is not an
operator claim that every provider works on an unconfigured host.

Research inputs:

- [Local implementation research](../../../01_research/local/llm_caret_spipe_infra_access_hardening.md)
- [Provider/interface research](../../../01_research/domain/llm_caret_spipe_infra_access_hardening.md)
- [Selected feature requirements](../../../02_requirements/feature/llm_caret_spipe_infra_access_hardening.md)
- [Selected NFRs](../../../02_requirements/nfr/llm_caret_spipe_infra_access_hardening.md)
- [Architecture](../../../04_architecture/llm_caret_spipe_infra_access_hardening.md)
- [Detail design](../../../05_design/llm_caret_spipe_infra_access_hardening.md)

## Baseline truth before this lane

At the research baseline, LLM Caret and ITF were separate.

- The LLM Caret permission gate recognizes only `bash`, `read_file`,
  `write_file`, `list_dir`, and `glob`.
- LLM Caret imports no ITF module and exposes no typed repository, task,
  storage, mail, or wiki tool.
- ITF dispatches Jira, Confluence wiki, Bitbucket, MinIO, Outlook, raw API,
  authentication, and daily-debug commands.
- GitHub is an undispatched `gh` passthrough marked as a stub.
- Gmail and GitHub Wiki adapters did not exist at that baseline.
- The wired Bitbucket, Outlook, and Confluence pure-Simple paths build request
  data but lack proven production transport.
- Most current live evidence uses separate curl or `mc` fallback adapters; that
  does not prove the provider path wired by each production command.
- The SPipe process harness normalizes LLM events and manages state/gates, but
  it does not own infrastructure service access.

Therefore, "request builder exists," "fixture parser passes," and "provider is
usable from Caret" are three different claims. Evidence must keep them separate.

## Canonical compatibility interfaces

The selected design uses familiar contracts instead of a new universal
lowest-common-denominator CLI. Capability output remains authoritative for each
provider-specific subset.

| Category | Canonical contract | Provider mapping |
|---|---|---|
| Repository hosting | GitHub CLI `gh` | GitHub is native. Bitbucket PRs and GitLab merge requests map to `gh pr` where semantics agree. Provider-specific pipelines, permissions, and fields remain capabilities or raw API operations. |
| Task management | `acli jira` | Jira work items are native. GitHub Issues can implement a smaller issue profile. Labels map directly; milestones map to fix versions or sprints only through explicit configuration. JQL, boards, workflows, and custom fields remain provider-native. |
| Object storage | `aws s3` and `aws s3api` | AWS S3 is native. MinIO changes endpoint, credentials, addressing, and signing configuration while preserving `s3://` paths and S3 operation semantics. `mc` is a fallback/tooling surface, not the canonical object model. |
| Mail | Gmail REST resources | Gmail threads, messages, labels, drafts, attachments, history, and watch form the common model. Microsoft Graph folders, categories, conversations, drafts, and send operations map only where meanings agree. MIME and provider IDs remain available. |
| Wiki | Neutral `wiki page list|get|create|update|delete` plus search/raw | Confluence REST pages preserve page ID, space, parent, body representation, and version. GitHub Wiki maps pages to Markdown files and git commits in the wiki repository. |

There is no stable universal mail CLI and no universal official wiki CLI. The
mail and wiki contracts are semantic interfaces, not claims of command-line
parity with a nonexistent standard.

## Conversion rules

Compatibility conversion must preserve provider reality:

- Provider names and resource IDs stay distinct and observable.
- Pagination cursors such as `nextPageToken`, `@odata.nextLink`, and Bitbucket
  `next` URLs remain opaque.
- Provider error code, HTTP status, request ID, and retry metadata survive
  normalization.
- Raw provider operations remain available for features outside the common
  contract.
- Unsupported operations return an explicit capability error.
- Lossy conversion requires explicit opt-in or is rejected.

Examples of intentionally non-lossless mappings include Jira workflows to
GitHub issue state, Graph folders to Gmail labels, and Confluence storage-format
HTML to GitHub Wiki Markdown. The adapter must not manufacture reversibility.

## Permission and security behavior

Every infrastructure operation must traverse the LLM Caret permission gate;
unrestricted `bash` is not the service API.

The proposed policy classes are:

1. Read operations: list, get, search, view, status.
2. Write operations: create, update, comment, upload, send.
3. Destructive operations: delete, merge, move with deletion, overwrite, or
   transition with irreversible effect.
4. Authentication operations: login, token refresh, credential validation.

Mutations are denied by default. Destructive operations require an additional
explicit grant and should support dry-run when the provider does. Secrets enter
through stdin, a credential store, or environment indirection; they never enter
argv, logs, model-visible diagnostics, or captured test output.

Retries are bounded and honor provider retry guidance. Reads and idempotent
operations may retry retryable throttling or 5xx failures. Writes are not
blindly replayed; retry requires a provider idempotency key, conditional write,
known request outcome, or explicit operator decision.

Downloaded paths and filenames remain workspace-confined. Large objects and
attachments stream rather than requiring whole-payload buffering. Provider
processes have a 120-second deadline and 30,000-byte pre-capture output bound.

## Implemented Caret tool contract

The selected implementation registers five names behind `run_tool`:

| Tool | Providers currently routed |
|---|---|
| `infra_repo` | GitHub through `gh`; mapped Bitbucket PR subset through `bin/simple itf bb` |
| `infra_task` | Jira through `acli jira`; GitHub Issues through `gh issue` |
| `infra_storage` | S3/MinIO through `aws s3` and `aws s3api` |
| `infra_mail` | Gmail resources through provisional `gws gmail`; Outlook subset through `bin/simple itf outlook` |
| `infra_wiki` | Confluence through `bin/simple itf wiki`; GitHub Wiki reads through direct `git`, mutations/raw through `bin/simple itf github-wiki` |

Each call uses scalar JSON fields: `provider`, `operation`, optional `args`,
`format`, `endpoint`, and `raw_safety`. `args` is one direct argv item per
newline. Spaces inside a line remain inside one argument; no shell tokenizer or
interpolation runs.

Examples:

```json
{"provider":"","operation":"capabilities","format":"json"}
```

```json
{"provider":"github","operation":"pr.view","args":"42\n--repo\norg/project","format":"json"}
```

```json
{"provider":"minio","operation":"s3.cp","args":"s3://bucket/key\nbuild/downloads/key.bin","endpoint":"https://minio.example","format":"human"}
```

```json
{"provider":"github","operation":"page.update","args":"--repo-path\nbuild/wiki\n--page\nHome.md\n--from-file\ndoc/Home.md","format":"json"}
```

Read operations and capability discovery follow the existing automatic-read
policy. Configure grants such as `infra_task:write` or `infra_mail:auth` for
ordinary mutations/authentication. A destructive operation requires its exact
family key, for example `infra_repo:destructive`; granting only `infra_repo`
does not permit merge/delete/close operations. Raw provider argv additionally
requires `raw_safety=read|write|destructive|auth`.

Capability output is a contract inventory, not executable discovery. If `gh`,
`acli`, `aws`, `gws`, or the configured Simple/ITF route is absent or
unauthenticated, the real call fails with that route's exit status. On the
qualification host used during implementation, `gh` and `git` were present;
`acli`, `aws`, and `gws` were absent, so no live claim is made for them.

GitHub Wiki operations require a local clone of `<repo>.wiki.git` supplied by
`--repo-path`. Create/update take `--from-file`; delete requires `--yes`; each
mutation creates a git commit with `--message` or a deterministic default.

## Test and evidence model

The default evidence baseline is deterministic and offline unless the selected
NFR makes live tests mandatory.

Offline contract tests should prove:

- tool registration and permission classification;
- canonical argument conversion and validation;
- provider capability discovery and explicit unsupported behavior;
- opaque ID and pagination preservation;
- error normalization without secret leakage;
- retry classification and bounds;
- mutation/destructive denial by default;
- workspace path confinement;
- stable human, JSON, and NDJSON output.

Live tests are separate evidence:

- read-only provider smoke tests are opt-in under the production-balanced NFR;
- write/destructive tests require disposable fixtures and an explicit enable
  variable or grant;
- each test records which adapter and transport actually ran;
- fallback evidence is not attributed to an unwired pure-Simple adapter.

SPipe must provide an executable behavioral feature spec in `test/03_system`
and a generated/manual Markdown companion under `doc/06_spec`. Assertions must
exercise real conversion, permission, error, and provider-selection behavior;
trace tables and file-count checks are insufficient.

An evidence ledger should record the canonical operation, provider, resource
ID, safety class, adapter, transport, offline/live status, response class,
retry decision, and whether a destructive grant was required.

## Implementation and verification checklist

The user selected A + 2 on 2026-07-18:

1. Final REQ/NFR documents replace the deleted option files.
2. Reconcile older Claude-full LOC/source-shape completion gates with current
   behavioral requirements; do not silently claim full Claude CLI parity.
3. Design the selected Caret-to-ITF/shared-capsule boundary without duplicating
   provider transport inside Caret.
4. Define shared tool names, setup helpers, checker helpers, and fail-fast SPipe
   placeholders before parallel implementation begins.
5. Create architecture, detail design, system-test plan, executable SPipe spec,
   generated manual, and agent task plan with sidecar lanes, merge owner, and
   high-capability final reviewer.
6. Wire and test the actual production adapter path for each selected provider.
7. Gmail and GitHub Wiki are selected; capability output must distinguish
   provisional/missing routes from tested production routes.
8. Run each focused acceptance check once, with no more than three fix/verify
   cycles, and stop when evidence converges.

## Evidence boundary

Offline conversion and injected-runner tests prove the Caret boundary and exact
route plan. They do not prove provider credentials, network availability, or a
live remote mutation. Live evidence is opt-in and must name its actual adapter
and transport; this guide still does not claim full Claude CLI parity.
