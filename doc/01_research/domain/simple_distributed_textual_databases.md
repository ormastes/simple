<!-- codex-research -->
# Domain research: Git- and CI-connected textual databases

**Date consulted:** 2026-09-13  
**Status:** Primary-source research and engineering synthesis

## Git settlement and Git servers

Git `receive-pack` quarantines incoming objects before accepting refs. A `pre-receive` hook can reject the entire proposed ref set; an `update` hook evaluates individual refs; `post-receive` is notification and cannot roll back an accepted update. Self-hosted adapters may use these hooks for additional admission, but hosted services do not portably expose arbitrary hooks, so SCV cannot require them. [Git receive-pack](https://git-scm.com/docs/git-receive-pack), [Git hooks](https://git-scm.com/docs/githooks.html)

Atomic multi-ref push is negotiated only when the server advertises the `atomic` capability and the client requests it. The portable settlement transaction should therefore be one candidate commit and one protected canonical ref compare-and-swap/fast-forward; inbox refs are discovery aids, not part of the identity transaction. [Git protocol capabilities](https://git-scm.com/docs/protocol-capabilities.html)

Git's wire protocol does not supply application actor authorization. Transport authentication, Git-server branch protection, and SCV operation-level authorization are distinct layers. [Git pack protocol](https://git-scm.com/docs/gitprotocol-pack)

For ordinary non-forced branch updates, Git accepts the update only when the new commit is a descendant of the current ref tip; force/update policy can override that rule, so the settlement ref must prohibit force and deletion and validate the expected old OID. [Git push](https://git-scm.com/docs/git-push)

Git garbage collection preserves reachable objects. Adding a compact checkpoint on a live branch therefore does not reclaim reachable batches, evidence, aliases, or secrets in prior commits; physical retention requires unreachable history, separate epochs/archives, and honest residual-copy reporting. [Git garbage collection](https://git-scm.com/docs/git-gc)

Required provider capability discovery includes exact fetch, expected-old-OID ref update or an admitted single-integrator equivalent, force/delete protection, authorization/audit evidence, object format, object/pack/ref limits, and read-back verification. A server missing mandatory settlement capabilities is unsupported for allocator authority; it must not silently degrade.

### Gitea and Forgejo

Gitea protected-branch rules apply across Git protocols, the web editor, API, and background jobs. Current rules can make a branch read-only, allowlist ordinary push, keep force push disabled, and require signed commits. Its API exposes those protection controls, but documentation alone does not establish every deployed server/version's delete rejection or administrator-bypass posture. [Gitea protected branches](https://docs.gitea.com/usage/access-control/protected-branches/), [Gitea branch-protection API](https://docs.gitea.com/api/1.24/operations/repo-create-branch-protection/)

Forgejo delegates repository operations to its installed Git binary and provides protected-branch policy. Custom repository hooks are disabled by default because enabling them lets privileged users execute code as the Forgejo OS user; they cannot be a portable tenant requirement. Forgejo API tokens support repository scoping, and workflow-token writes do not recursively trigger workflows, so reconciliation remains mandatory. [Forgejo repository protection](https://forgejo.org/docs/v15.0/user/repository/protection/), [Forgejo architecture](https://forgejo.org/docs/latest/contributor/architecture/), [Forgejo configuration](https://forgejo.org/docs/v16.0/admin/config-cheat-sheet/), [Forgejo token scopes](https://forgejo.org/docs/v15.0/user/authentication/token-scope/), [Forgejo Actions concepts](https://forgejo.org/docs/v16.0/user/actions/basic-concepts/)

Forgejo quotas are soft and may be exceeded by an admitted Git push because final packed size is not known in advance. Its API/UI size limits do not establish receive-pack object limits, and inspected official documentation does not establish SHA-256 object-format interoperability. SCV must bound candidate bytes itself, probe the deployed Git/Forgejo versions and object format, avoid hard-coded 40-character OIDs, and never use force-push mirrors for settlement. [Forgejo quotas](https://forgejo.org/docs/latest/admin/advanced/quota/), [Forgejo repository mirrors](https://forgejo.org/docs/latest/user/repo-mirror/)

The Gitea/Forgejo conformance suite therefore needs concurrent normal pushes, force/delete rejection, administrator bypass configuration, uncertain acknowledgement, scoped credentials, object-format negotiation, batch limits, and workflow-trigger suppression. Settlement publishes one Git commit/tree, not a sequence of file-content API updates.

## CI servers

A provider-neutral run envelope defines nullable canonical dimensions for provider instance, tenant/project/repository, workflow/pipeline, run, attempt, job, shard/matrix case, test case, observation revision, source OID, and immutable manifest digest. Each adapter declares which dimensions it can supply and a capability-specific uniqueness tuple; missing inapplicable dimensions are explicit, never synthesized from branch-name `latest`.

GitHub exposes workflow-run IDs, attempts, head SHA, status/conclusion, and artifact metadata through REST. Artifact records include expiry and a digest. Failed webhook deliveries are not automatically redelivered, so polling/reconciliation is required. [GitHub workflow runs](https://docs.github.com/en/rest/actions/workflow-runs), [GitHub artifacts](https://docs.github.com/en/rest/actions/artifacts), [failed webhook deliveries](https://docs.github.com/en/webhooks/using-webhooks/handling-failed-webhook-deliveries), [webhook redelivery](https://docs.github.com/en/webhooks/testing-and-troubleshooting-webhooks/redelivering-webhooks)

GitHub workflow credentials should receive the minimum required permissions; when the built-in token lacks required scope, a GitHub App token is the documented expansion path. The privileged textual-DB publisher must be separated from untrusted test execution and must not expose credentials to fork-controlled code. [GitHub Actions token permissions](https://docs.github.com/en/actions/security-guides/automatic-token-authentication)

GitLab supports pipeline triggers and job/pipeline webhooks. Push events can be suppressed when a push exceeds configured ref-change limits. Artifact APIs support retrieval, keep, and deletion, while retention defaults and latest-success rules affect availability. [GitLab pipeline triggers](https://docs.gitlab.com/api/pipeline_triggers/), [GitLab webhook events](https://docs.gitlab.com/user/project/integrations/webhook_events/), [GitLab webhooks](https://docs.gitlab.com/user/project/integrations/webhooks/), [GitLab artifact API](https://docs.gitlab.com/api/job_artifacts/), [GitLab job artifacts](https://docs.gitlab.com/ci/jobs/job_artifacts/)

Jenkins exposes object-scoped remote APIs for querying and triggering work. Rich behavior varies with server version and plugins. `archiveArtifacts` is basic build-associated archival governed by build retention, not a permanent evidence store. [Jenkins remote API](https://www.jenkins.io/doc/book/using/remote-access-api/), [Jenkins pipeline](https://www.jenkins.io/doc/book/pipeline/jenkinsfile/), [Jenkins pipeline syntax](https://www.jenkins.io/doc/book/pipeline/syntax/)

Buildkite build and job UUIDs provide stable identities, while build numbers are only pipeline-scoped. Retries retain prior jobs and create linked new jobs, so each attempt must remain distinct. Webhooks are HMAC-authenticated hints whose embedded object may already be stale; ingestion fetches current build/jobs and reconciles with an overlapping cursor. Managed artifacts retain provider metadata including SHA-1, but SCV must compute its own SHA-256 and copy pinned evidence before the documented managed-storage expiry. Short-lived OIDC identifies workload context; it does not attest artifact bytes without a bound manifest signature/digest. [Buildkite builds API](https://buildkite.com/docs/apis/rest-api/builds), [Buildkite jobs API](https://buildkite.com/docs/apis/rest-api/jobs), [Buildkite retries](https://buildkite.com/docs/pipelines/configure/retry), [Buildkite webhooks](https://buildkite.com/docs/apis/webhooks/pipelines), [Buildkite artifacts](https://buildkite.com/docs/apis/rest-api/artifacts), [Buildkite OIDC](https://buildkite.com/docs/pipelines/security/oidc)

Azure Pipelines exposes build IDs plus plan, job, stage, and attempt identities; timeline records retain hierarchy and prior-attempt relationships. Service hooks can exhaust retries, so build-complete events require Builds/Timeline polling and overlap reconciliation. Artifact metadata does not provide one portable cryptographic digest contract, and run deletion removes artifacts and related evidence; SCV computes SHA-256 and archives pinned content independently. [Azure pipeline variables](https://learn.microsoft.com/en-us/azure/devops/pipelines/build/variables?view=azure-devops), [Azure build API](https://learn.microsoft.com/en-us/rest/api/azure/devops/build/builds/get?view=azure-devops-rest-7.1), [Azure timeline API](https://learn.microsoft.com/en-us/rest/api/azure/devops/build/timeline/get?view=azure-devops-rest-7.1), [Azure service-hook events](https://learn.microsoft.com/en-us/azure/devops/service-hooks/events?view=azure-devops), [Azure artifact API](https://learn.microsoft.com/en-us/rest/api/azure/devops/build/artifacts/list?view=azure-devops-rest-7.1), [Azure retention](https://learn.microsoft.com/en-us/azure/devops/pipelines/policies/retention?view=azure-devops)

Azure Repos' ref-update API accepts exact old and new object IDs and explicitly reports a stale old object, which is a direct settlement CAS capability. Branch policy and permission configuration must deny force push and broad policy bypass; if required policy blocks direct update, the adapter needs a tightly scoped admitted settlement principal or a revalidating merge path rather than pretending an ordinary PR merge is allocation settlement. [Azure Repos ref update](https://learn.microsoft.com/en-us/rest/api/azure/devops/git/refs/update-refs?view=azure-devops-rest-7.1), [Azure branch policies](https://learn.microsoft.com/en-us/azure/devops/repos/git/branch-policies?view=azure-devops), [Azure repository security](https://learn.microsoft.com/en-us/azure/devops/repos/git/secure-repositories-pull-requests?view=azure-devops)

These systems support three adapter modes: push/event hints, paginated pull/reconciliation, and immutable bundle-only publication. A provider may implement any subset. Cursor advancement occurs only after normalized operations are durably recorded; producer acknowledgement occurs only after an immutable discoverable manifest is durable.

## jj and Git compatibility

jj uses Git commits/files for collaboration, while bookmarks and higher-level metadata need explicit handling. Current documentation identifies incomplete support for Git features including submodules and LFS. The design should explicitly export/push the settlement bookmark/ref, avoid `.jj` internals, and not require submodules, merge drivers, hooks, or LFS in the portable path. [jj Git compatibility](https://docs.jj-vcs.dev/latest/git-compatibility/), [jj comparison with Git](https://docs.jj-vcs.dev/latest/git-comparison/)

## Prior art boundaries

- Datomic demonstrates explicit temporary-to-resolved identity mapping, but transaction-local tempids are not an offline replication protocol. [Datomic transaction data](https://docs.datomic.com/transactions/transaction-data-reference.html), [Datomic client transact result](https://docs.datomic.com/client-api/datomic.client.api.html#var-transact)
- SQLite Session demonstrates primary-key/before-value conflict detection, not a complete distributed database. [SQLite Session](https://sqlite.org/sessionintro.html)
- git-bug demonstrates offline Git-distributed issue data and provider bridges, not this schema or settlement policy. [git-bug](https://github.com/git-bug/git-bug)
- pytest demonstrates conditional expected failure and XPASS classification, reinforcing separation of actual outcomes from expectation policy. [pytest skip/xfail](https://docs.pytest.org/en/stable/how-to/skipping.html)

## Domain conclusions

1. Define `GitSettlementTransport`, not a GitHub-only backend.
2. Exactly one fenced authority may allocate within a namespace/epoch; mirrors are read-only.
3. Define `CiObservationSource` capability discovery for event, poll, bundle, artifact, attestation, pagination, and retention semantics.
4. Treat webhooks as latency hints and provider artifacts as expiring locations until verified into controlled content-addressed storage.
5. Separate authenticated provider identity, signed patch provenance, role/field/operation authorization, and Git ref protection.
6. Retain canonical semantic intent and acceptance receipts; keep replica-local leases/backoff disposable.
7. Refuse unsupported server capabilities, stale authority epochs, regressed high-water marks, and incompatible schema/reducer versions.
