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
- The executable release SSpec contains seven real scenarios, including
  mutation-free bidirectional `main`/release convergence and independent-trunk
  rejection. Its standalone
  manual was manually synchronized with the final source because the docgen
  lane had reached the mandatory three-cycle retry cap.

## Focused verification recorded in this lane

- Release policy/system SSpec: PASS (7/7 in the recorded focused run).
- Guarded release CLI: PASS (12/12 in the recorded focused run).
- Git convergence focused integration: implemented with exact repository
  fixtures; final real-Git test PASS (1/1).
- Persisted candidate authority: PASS (3/3), covering create-once state,
  admission binding, status, and promote-without-rebuild planning.
- Focused trusted-session lifecycle: PASS (1/1), covering register, lease,
  commit, registered-head compare-and-swap advance, verify, cleanup, close, and
  rejection of use after close.
- Protected-ref policy: PASS (28/28 adversarial command cases) and PASS (3/3
  cross-surface checks) across `sj`, Simple JJ sync, both MCP runtime families,
  and their prompts. Raw ref mutation and malformed work-bookmark pushes fail
  closed.
- Workflow source contracts: whole release gate PASS (4/4), provider-bound PR
  admission PASS (3/3), and release archive,
  immutable artifact identity, and publication chain PASS (3/3).
- Spipe release/plugin parity: PASS in the recorded plugin build run.
- Direct environment/runtime facade guards: PASS for working and staged scans.
- Source/workflow safety checks reject direct protected-ref mutation, broad tag
  pushes, rebuild/fallback promotion, and destructive tag rollback.
- Stage-2 frontend admission now native-builds and executes the exact Stage-3
  module-name paths, including a non-ASCII workspace prefix, with fallback
  disabled, an isolated cache, exact stdout, timeouts, log caps, and dead-lexer
  rejection. Its mocked fail-closed contract passes 8/8 and xhigh review found
  no P0/P1 defect.
- Live GitHub policy baseline: PASS. Seven projected rulesets, the declared
  protected-integration/release/npm-release environments, and immutable
  releases pass `scripts/release/github-policy.shs verify-live ormastes/simple`.

## Release-blocking evidence gaps

1. The locally available `simple` executable identifies itself as bootstrap
   seed-derived. It cannot establish the required release-grade lint and clean
   whole-suite PASS; no release admission may consume its result as such.
   A canonical `--full-bootstrap --release --strategy=full` attempt failed
   closed with exit 64 (`reason-receipt-required`): this workspace has no
   admitted parent/runtime/planner receipt identities, and inventing them would
   violate the bootstrap trust boundary. The sanctioned receipt-free Stage 2
   recovery then failed deterministically in
   `driver_hir_pipeline_lowering.spl`: the seed could not resolve
   `compiler.semantics.const_fold` (E1034). A bounded fetch/check of
   `origin/main` at `e35d34f9eeda1b899abd439c56aa8ecec674a1cf` found no fix. The
   defect and six related snapshot regressions were repaired in isolated lanes.
   Fragmented PRs #25/#26 are superseded by current-main PR #29. Its exact
   seven-fix closure admitted Stage 2 with provenance/sanity receipts and
   artifact SHA-256
   `a9c1b931648146c0ccf4f289dd2ab6176e1fd90b0db605338c84bacb406238b1`.
   Patch-equivalent copies were prepared in PR #28, which currently targets
   `main`; they are not protected `release/1.0` backports and no divergence
   receipt claims otherwise. Its first local bootstrap attempt
   correctly rejected a stale `1.0.0-RC` verifier literal; after binding every
   Stage 2/3 sanity consumer to canonical `release/version.sdn`, the second
   focused cycle admitted artifact SHA-256
   `609c9685ed03f752239de4dc20aba4d5baa97ecb6c6183fb994e9ea1fc76f071`.
   The final immutable-head Stage 2 cycle admitted artifact SHA-256
   `b06f4eb4f72a36f1b9250f20a9c0537c5aa98a9bb54a93792a947baf940b4511`
   and produced a verified Stage-3 planner receipt. Stage 3 then failed
   deterministically because the Stage-2-native module-name helper mapped
   `src/app/cli/bootstrap_main.spl` and `src/compiler/driver/driver.spl` to
   the empty name. The trunk correction is Simple PR #31; its exact reviewed
   admission-probe commit was copied into PR #28. PR #31 and the
   protected integration of PR #29 remain prerequisites to a fresh release
   lineage. Neither result updates a protected ref directly.
2. The GitHub policy configuration row is now PASS, but configuration is not a
   beta release receipt. Exact signed beta promotion, immutable publication of
   its admitted assets, artifact attestations, and byte-identical npm registry
   publication remain unexecuted and FAIL.

## Acceptance disposition

- Architecture, selected requirements/NFRs, operator guide, general software
  release skills, typed release/version/session/convergence implementation,
  Spipe plugin surfaces, candidate/promotion/publish workflows, and focused
  adversarial coverage are present and aligned.
- Production verification and actual beta release remain **FAIL** until both
  evidence gaps above pass. Missing evidence is not a warning and no
  fallback or inferred success is permitted.

## Required next evidence

1. Integrate trunk PRs #29 and #31 through protected review, create the actual
   protected `release/1.0` line, and backport the selected exact integrated
   revisions through isolated reviewed sessions with divergence receipts. Then start a fresh immutable
   Stage 2 lineage in a new bounded verification session. Produce admitted
   Stage 3 and Stage 4 artifacts and run the required lint plus one clean
   `bin/simple test test --whole --mode=interpreter` confirmation.
2. Using the verified live policy baseline, exercise one create-once beta
   candidate and promote its exact assets through signing, immutable GitHub
   publication, and byte-identical npm publication receipts.
