# Release Process Hardening Verification

**Status:** FAIL — implementation handoff, not beta-release-ready
**Branch:** `work/release/local-20260826-001-release-process-hardening`

## Evidence by acceptance area

- **AC-1, AC-6, AC-10, AC-12, AC-14:** implemented in the selected
  requirements/NFRs, architecture/design/plans, operator guide, skills, typed
  withdrawal policy, and clean working/staged runtime-facade guards.
- **AC-2:** repository-backed render/check/plan/apply and compatibility-aware
  bumping now cover canonical Simple and npm-registry projections. Guarded CLI
  integration passed 10/10, but its full-tree discovery exceeds NFR-008 and
  does not yet discover undeclared JSON consumers.
- **AC-3:** typed policy and active guides define isolated authoring/protected
  refs. Live GitHub policy verification remains blocked by
  `doc/08_tracking/bug/release_live_policy_verifier_missing_2026-08-26.md`.
- **AC-4, AC-5, AC-7:** typed receipt and trusted-session checks are implemented;
  focused release SSpec passed 6/6 and session authority passed 3/3. Candidate
  workflow contracts still omit required graph/creator/evidence identities.
- **AC-8, AC-9:** Spipe 0.2.0 guarded planning tools and projection build pass
  8/8, but parity coverage is incomplete and the planners are not Git-backed
  mutation authorities.
- **AC-11:** executable scenarios pass and no `.spl` exists under
  `doc/06_spec`; the manual requires regeneration after the final identity
  hardening and the documented adversarial matrix is not complete.
- **AC-13:** focused tests and plugin parity pass, but the available executable
  identifies itself as bootstrap seed-derived. Lint and the required whole
  suite therefore have no release-grade PASS.
- **AC-15:** this report deliberately leaves verification, release, and the
  thread goal incomplete.

## Independent highest-capability review

The final reviewer returned `STATUS: FAIL`. The requested convergence invariant
is now consistent in top-level rules, typed policy, bootstrap guidance, and
skills: discovery is read-only; selected fixes cross by reviewed isolated
backport/forward-port; `main` remains trunk. Remaining P0s are Git/CI wiring for
that discovery, divergent candidate/admission schemas, non-idempotent promotion,
npm rebuild-after-admission, incomplete projection parity, and version-check
latency/JSON discovery. These remain blockers, not warnings converted to PASS.

## Required next work

1. Wire convergence to bounded Git fetch/ref comparison and post-integration receipts.
2. Unify canonical candidate/admission schemas and support-manifest parsing.
3. Make promotion retries and remote asset verification idempotent.
4. Build/admit npm tarballs in candidate CI and publish them unchanged with correct prerelease tags.
5. Fix projection parity and bounded version-consumer indexing.
6. Regenerate and review the manual, complete adversarial CLI scenarios, then
   run lint and the whole suite with an admitted pure-Simple executable.
