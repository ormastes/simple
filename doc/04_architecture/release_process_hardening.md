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
- `src/app/release/version_policy.spl`: SemVer/channel and projection checks.
- `src/app/release/backport.spl`: reviewed beta bug-fix admission.
- `src/app/release/candidate.spl`: immutable candidate identity and admission facts.
- `src/app/release/promotion.spl`: signed exact-tag/no-rebuild/withdrawal plans.
- `src/app/release/main.spl`: CLI translation only; no duplicated policy.
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

## MDSOC evaluation

Release validation is cross-cutting, but an MDSOC feature transform would obscure the security boundary. Use a virtual capsule expressed by pure modules and immutable values. Provider adapters compose at the outer app boundary. No runtime weaving or per-OS release logic is required.

## Beta and backport flow

`BackportRequest` carries source commit, change ID, work ID, kind, source review, target `release/X.Y`, expected target SHA, adaptation reason, evidence digest, and tested result SHA. Validation returns a deterministic plan or one actionable error. The executor may cherry-pick only that exact source into a private session branch. It then obtains renewed evidence for the result revision before integration authority performs CAS.

The command must never accept “latest,” an unqualified branch, a range of commits, or an automatic set of fixes. Each bug fix has a separate provenance record.

## Main/release convergence

The bootstrap/release supervisor may run a bounded scheduled discovery task after fetch and at configured qualification checkpoints. The task compares immutable snapshots of `main` and the active `release/X.Y`, classifies reviewed `fix` changes, and emits proposals only. Discovery has no ref-write capability and cannot feed a cherry-pick executor directly.

An operator or integration authority selects an exact proposal. A `main` fix follows the normal backport path into a private release-line work branch. A fix first created on `release/X.Y` follows the symmetric forward-port path into a private `main`-targeted work branch. Adapted patches receive their own review. Both paths rerun focused evidence on the resulting commit and produce a divergence receipt containing source and target refs/SHAs, selected source commit, result commit, direction, review/evidence digests, omitted proposals with reasons, and remaining divergence. The protected integration authority performs the final CAS update. No scheduler, bootstrap worker, or ordinary session pushes a protected ref.

## Candidate and promotion boundary

Candidate creation is separate from builds. Builders consume the immutable manifest and publish content-addressed artifacts. Admission binds all required artifact/evidence digests. Promotion verifies the same digests and emits the exact signing/tag/publication plan; it never invokes a compiler or packager.

## Plugin boundary

Spipe plugin version `0.2.0` declares `spipe-vcs/3`, `spipe-session/1`, `spipe-release/1`, `spipe-candidate/1`, and release capabilities. Initial CLI/MCP additions are read/plan oriented and must not expose arbitrary Git commands. A future mutating provider consumes the same plan schema and explicit capability token.

## Error handling and observability

Pure checks return typed results with stable reason codes. CLI JSON includes command, status, reason, and identity digests but never secrets. Debug logging may show validation stages, not credentials or full environment. Maintenance projection checks may scan their declared finite file list once; request handlers cache parsed policy by content digest.

## Performance targets

Warm pure checks over supplied manifests target 250 ms and no network/process calls. Live policy drift is a separate explicit maintenance command. Candidate and promotion planning scale with declared artifacts/evidence rather than repository size.

## Security and recovery

The pure capsule cannot mutate refs. Adapters validate ref names and exact expected SHAs before execution. Release signing and GitHub publication remain approval-gated. Stale targets, policy drift, missing receipts, unsupported platforms, or unavailable signing produce BLOCKED/FAIL, never degraded PASS. Recovery produces a redeploy/withdrawal plan and never tag deletion.

## Consequences

- Existing `prepare.spl` becomes a legacy compatibility entry until callers move to the new CLI; its unsafe tag instructions must be removed.
- Tag-triggered build CI remains a release blocker until converted to candidate build plus promote-only publication.
- The first implementation can fully verify pure planning and projection parity without publishing or changing live GitHub configuration.
