<!-- codex-design -->

# Release Process Hardening Architecture

## Context and decision

Current Simple release surfaces split authority across `release/version.sdn`, `VERSION`, hard-coded source literals, release skills, `src/app/release/prepare.spl`, and tag-triggered CI. Spipe projections additionally encode direct-main and unsigned-tag behavior. This architecture makes policy and manifests authoritative and keeps external mutation behind explicit adapters.

Adopt a layered **plan → admit → promote** capsule:

```text
release/version.sdn + .spipe/policy/vcs.sdn
                    |
            ReleasePolicy capsule
          /          |           \
 Version projection  Beta/backport  Candidate/admission
          \          |           /
             PromotionPlan (pure)
                    |
       VCS / signer / GitHub adapters
```

The pure layer parses and validates caller-supplied facts and produces typed plans. It performs no Git, GitHub, signing, filesystem mutation, or build. Existing provider code may execute an accepted plan only after capability and approval checks.

## Ownership

- `release/version.sdn`: sole editable product version and projection list.
- `.spipe/policy/vcs.sdn`: sole ref/session/tag mutation policy.
- `src/app/release/policy.spl`: pure value types and invariant checks.
- `src/app/release/version_authority.spl`: manifest parsing, SemVer/channel,
  compatibility bumping, deterministic projection render/check/apply.
- `src/app/release/policy.spl`: reviewed backport, immutable candidate,
  qualification/admission, signed exact-tag/no-rebuild, and withdrawal values.
- `src/app/release/main.spl`: CLI translation only; no duplicated policy.
- `src/app/release/session_authority.spl`: canonical Git-worktree verification,
  repository-wide session registry, and private output/cache ownership.
- `src/app/release/convergence.spl`: bounded fetch-only main/release discovery
  and post-integration divergence receipts.
- `src/app/release/support_policy.spl`: parsed required support rows shared by
  candidate qualification and admission.
- `src/app/release/self_review_policy.spl`: pure external-policy, exact-state
  changed-path, honest evidence-mode, deny/constraint, and expiry evaluator.
- `.spipe/policy/self-review-policy.sdn`: non-authoritative checked-in projection;
  operator JSONL records remain external to the PR worktree.
- `.github/workflows/review-admission.yml`: protected-environment,
  trusted-default-branch workflow that resolves and re-resolves protected
  target/head/base/merge-base/diff, publishes a short-lived required check, and
  expires old successes without submitting provider Approve.
- `src/app/release/github.spl`: low-level provider; callable only after admission.
- `examples/05_stdlib/spipe/`: canonical embedded plugin package and generated operator/model projections.

## Core values

`ReleaseVersion`, `ReleaseChannel`, `ReleasePolicy`, `ReleaseSession`, `BackportRequest`, `CandidateManifest`, `ReleaseAdmission`, `PromotionPlan`, and `ReleaseReceipt` are explicit values. Identity-bearing canonical text never includes host paths, credentials, or wall-clock time.

## Invariants

1. New versions use stable or lowercase numbered alpha/beta/RC grammar.
2. Channel and suffix agree.
3. A release mutation requires a non-main workspace, owned work branch, exact base/target SHA, and policy hash.
4. Beta backports accept only reviewed `fix` changes and bind renewed evidence to the post-application revision.
5. Candidate identity binds exact version, attempt, commit, source/policy/version/toolchain/support/evidence digests.
6. Candidate creation is create-once; a changed input creates a new attempt.
7. Promotion binds the admitted commit and artifact manifest, requires a signed annotated exact tag plan, and forbids rebuilding/fallback/all-tag push.
8. Withdrawal preserves identity; correction increments version.
9. `main` remains the development trunk; a maintenance line is never its upstream, replacement, or tracking target.
10. Periodic main/release discovery is read-only. Only an explicit reviewed convergence plan may cross a fix between protected lines.
11. Convergence inventory is computed at a reviewed pre-administration boundary; manifest-only commits and the final integration merge are outside that inventory, avoiding commit self-reference.
12. Provider evidence is accepted only for configured check-name/App identities, and every backport or forward port must be stable-patch-ID equivalent to its exact source commit with an aligned provider review/check receipt. Adapted equivalence is a separate future authority path.
13. Ordinary code/text defaults allow after explicitly authorized `self_attested` PASS with zero P0/P1; that evidence is never labeled authenticated or independent, and external deny/constraints win.
14. Rename checks old+new, delete old, copy new. Traversal, path aliases, symlink, submodule, non-UTF-8, actual secrets, stale target/head/base/diff/ruleset, malformed policy/hash chain, and dishonest evidence deny.
15. A self-review decision creates no provider approval or permanence claim. It binds the normalized ruleset digest, expires in ten minutes, and is reset by trusted PR/base/policy events with scheduling as backup. Candidate admission accepts only `spipe-review-admission/1`; protected release/npm environment review remains separate.

## Scoped self-review boundary

The provider rulesets replace an unsatisfiable sole-owner Approve requirement
with the GitHub-Actions-owned `SPipe Self Review Admission` status on the exact
PR head. The workflow reads an operator-owned external JSONL deny/constraint
database, generates the changed-path manifest from exact fetched
base/merge-base/head Git objects, binds the protected target ruleset, and
invokes the pure evaluator. This makes the policy source
reviewable without letting a PR edit its own live authority. The check-run
adapter consumes only an allowed decision and still records
`provider_approval_claimed=false`.

The external records are append/hash-chain shaped, signed by an operator key,
and bind repository numeric/node/name identity, PR, head, session, reviewer,
manifest/evidence digest, issuer, and a maximum 24-hour record window. `deny`
rejects the exact binding. `constrain` intersects allow scopes;
its deny scopes take precedence. No matching record means default allow for
ordinary reviewed code/text. Credential/secret semantics remain an immutable
denial independent of path rename.

By user decision, App ID 15368 is a generic GitHub Actions trust identity, not
an independent broker. Read-only repository defaults and the protected
`self-review-admission` environment constrain the intended workflow but cannot
eliminate same-repository context spoofing. This accepted risk is explicit.

## MDSOC evaluation

Release validation is cross-cutting, but an MDSOC feature transform would obscure the security boundary. Use a virtual capsule expressed by pure modules and immutable values. Provider adapters compose at the outer app boundary. No runtime weaving or per-OS release logic is required.

## Beta and backport flow

`BackportRequest` carries source commit, change ID, work ID, kind, source review, target `release/X.Y`, expected target SHA, adaptation reason, evidence digest, and tested result SHA. Validation returns a deterministic plan or one actionable error. The executor may cherry-pick only that exact source into a private session branch. It then obtains renewed evidence for the result revision before integration authority performs CAS.

The command must never accept “latest,” an unqualified branch, a range of commits, or an automatic set of fixes. Each bug fix has a separate provenance record.

## Main/release convergence

The bootstrap/release supervisor may run a bounded scheduled discovery task after fetch and at configured qualification checkpoints. The task compares immutable snapshots of `main` and the active `release/X.Y`, classifies reviewed `fix` changes, and emits proposals only. Discovery has no ref-write capability and cannot feed a cherry-pick executor directly.

An operator or integration authority selects an exact proposal. A `main` fix follows the normal backport path into a private release-line work branch. A fix first created on `release/X.Y` follows the symmetric forward-port path into a private `main`-targeted work branch. The current admission path requires exact stable-patch-ID equivalence; adapted patches need a separate future reviewed equivalence authority and fail closed here. Both paths rerun focused evidence on the resulting commit and produce a divergence receipt containing source and target refs/SHAs, selected source commit, result commit, direction, review/evidence digests, omitted proposals with reasons, and remaining divergence. The protected integration authority performs the final CAS update. No scheduler, bootstrap worker, or ordinary session pushes a protected ref.

## Candidate and promotion boundary

Candidate creation is separate from builds. Builders consume the immutable manifest and publish content-addressed artifacts, including the already-packed npm registry tarballs. Candidate, qualification, and admission use one versioned schema family and bind source, policy, version, toolchain, support, build graph, creator, evidence, convergence, qualification, and artifact identities. Promotion verifies the same digests and emits the exact signing/tag/publication plan; it never invokes a compiler or packager. Remote execution is retry-idempotent: an existing tag must verify against the same commit and admission digest, existing assets must be byte-identical, and published releases cannot acquire missing or replacement assets.

## Plugin boundary

Spipe plugin version `0.2.0` declares `spipe-vcs/3`, `spipe-session/1`, `spipe-release/1`, `spipe-candidate/1`, and release capabilities. Initial CLI/MCP additions are read/plan oriented and must not expose arbitrary Git commands. A future mutating provider consumes the same plan schema and explicit capability token.

## Error handling and observability

Pure checks return typed results with stable reason codes. CLI JSON includes command, status, reason, and identity digests but never secrets. Debug logging may show validation stages, not credentials or full environment. Maintenance projection checks may scan their declared finite file list once; request handlers cache parsed policy by content digest.

## Performance targets

Warm pure checks over supplied manifests target 250 ms and no network/process calls. Live policy drift is a separate explicit maintenance command. Candidate and promotion planning scale with declared artifacts/evidence rather than repository size.

## Security and recovery

The pure capsule cannot mutate refs. Adapters validate ref names and exact expected SHAs before execution. Release signing and GitHub publication remain approval-gated. Stale targets, policy drift, missing receipts, unsupported platforms, or unavailable signing produce BLOCKED/FAIL, never degraded PASS. Recovery produces a redeploy/withdrawal plan and never tag deletion.

## Consequences

- Existing `prepare.spl` is a fail-closed legacy entry while callers move to the guarded CLI.
- Candidate CI builds and admits exact assets; release CI promotes without rebuilding; npm publication consumes the admitted tarballs unchanged.
- Repository implementation still cannot prove live provider policy, signing, immutable publication, or release-grade bootstrap evidence without executing those authorities.
