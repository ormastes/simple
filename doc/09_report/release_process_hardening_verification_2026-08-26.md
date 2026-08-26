# Release Process Hardening Verification

**Status:** FAIL — implementation substantially complete; release-grade evidence incomplete
**Branch:** `work/release/local-20260826-001-release-process-hardening`

## Implemented evidence

- Canonical version parsing, compatibility-aware bump planning/apply, and
  deterministic Simple plus npm projection checks are repository-backed.
- Trusted release-session authority validates canonical linked-worktree Git
  state and registers unique session/workspace/branch ownership under a lock,
  with private output and cache-overlay namespaces.
- Beta/main convergence performs bounded fetch-only Git comparison, exact
  reviewed selection checks, ancestry and patch-equivalence checks, and
  post-integration divergence receipts. It never applies or pushes; `main`
  remains the independent trunk.
- Candidate CI emits one schema family for candidate, qualification, and
  admission evidence, binds build graph, creator, support, convergence,
  qualification, artifact, and provenance identities, and admits candidate-built
  MCP/LSP npm tarballs.
- Promotion CI is promote-only and retry-idempotent: an existing tag must match
  signature, commit, and admission digest; draft and published assets must have
  exactly the admitted names and bytes. It contains no build/fallback path.
- npm publication verifies immutable-release evidence and admitted tarball
  bytes, publishes the tarballs unchanged with channel-aware distribution tags,
  and accepts a retry only when registry bytes and tag already match.
- Spipe 0.2.0 guarded release planners, CLI/MCP descriptions, general release
  skills, and projection parity checks describe the same trust boundaries.
- The executable release SSpec contains six real scenarios. Its standalone
  manual was manually synchronized with the final source because the docgen
  lane had reached the mandatory three-cycle retry cap.

## Focused verification recorded in this lane

- Release policy/system SSpec: PASS (6/6 in the recorded focused run).
- Guarded release CLI: PASS (10/10 in the recorded focused run).
- Git convergence focused integration: implemented with exact repository
  fixtures; final real-Git test PASS (1/1).
- Persisted candidate authority: PASS (3/3), covering create-once state,
  admission binding, status, and promote-without-rebuild planning.
- Protected-ref policy: PASS (28/28 adversarial command cases) and PASS (3/3
  cross-surface checks) across `sj`, Simple JJ sync, both MCP runtime families,
  and their prompts. Raw ref mutation and malformed work-bookmark pushes fail
  closed.
- Workflow source contracts: whole release gate PASS (2/2) and release archive,
  immutable artifact identity, and publication chain PASS (3/3).
- Spipe release/plugin parity: PASS in the recorded plugin build run.
- Direct environment/runtime facade guards: PASS for working and staged scans.
- Source/workflow safety checks reject direct protected-ref mutation, broad tag
  pushes, rebuild/fallback promotion, and destructive tag rollback.

## Release-blocking evidence gaps

1. The locally available `simple` executable identifies itself as bootstrap
   seed-derived. It cannot establish the required release-grade lint and clean
   whole-suite PASS; no release admission may consume its result as such.
   A canonical `--full-bootstrap --release --strategy=full` attempt failed
   closed with exit 64 (`reason-receipt-required`): this workspace has no
   admitted parent/runtime/planner receipt identities, and inventing them would
   violate the bootstrap trust boundary.
2. The full trusted-session registry integration spec exceeded its bounded
   timeout. Source checking and persisted candidate authority pass, but the
   complete register/lease/head-advance/cleanup/close scenario still requires a
   fresh bounded PASS.
3. Repository workflow source is not live-provider evidence. GitHub rulesets,
   protected environments, signing identity, immutable-release configuration,
   artifact attestations, and npm registry publication require successful live
   receipts before a beta can be declared released.

## Acceptance disposition

- Architecture, selected requirements/NFRs, operator guide, general software
  release skills, typed release/version/session/convergence implementation,
  Spipe plugin surfaces, candidate/promotion/publish workflows, and focused
  adversarial coverage are present and aligned.
- Production verification and actual beta release remain **FAIL** until all
  three evidence gaps above pass. Missing evidence is not a warning and no
  fallback or inferred success is permitted.

## Required next evidence

1. Produce an admitted pure-Simple runtime and run the required lint plus one
   clean `bin/simple test test --whole --mode=interpreter` confirmation.
2. Diagnose the trusted-session timeout and obtain one bounded integration PASS
   without weakening canonical Git/session checks.
3. Apply/verify live rulesets and protected environments, then exercise one
   create-once beta candidate and promote its exact assets through signing,
   immutable GitHub publication, and byte-identical npm publication receipts.
