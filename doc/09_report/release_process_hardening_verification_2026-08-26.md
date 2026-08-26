# Release Process Hardening Verification

**Status:** FAIL — implementation handoff, not beta-release-ready
**Branch:** `work/release/local-20260826-001-release-process-hardening`

## Evidence by acceptance area

- **AC-1, AC-6, AC-10, AC-12, AC-14:** implemented in the selected
  requirements/NFRs, architecture/design/plans, operator guide, skills, typed
  withdrawal policy, and clean working/staged runtime-facade guards.
- **AC-2:** canonical projections agree on `1.0.0-rc.1`; focused version
  manifest spec passed 5/5. Required repository-backed render/check/bump and
  compatibility-aware bumping are not implemented.
- **AC-3:** typed policy and active guides define isolated authoring/protected
  refs. Live GitHub policy verification remains blocked by
  `doc/08_tracking/bug/release_live_policy_verifier_missing_2026-08-26.md`.
- **AC-4, AC-5, AC-7:** pure policy checks and focused SSpec passed 6/6,
  including beta-only fixes, candidate immutability, promote-not-rebuild, and
  withdrawal. They still consume caller-asserted identities rather than
  verified session/review/admission receipts; the legacy prepare entrypoint is
  now fail-closed.
- **AC-8, AC-9:** Spipe manifest/projections are at 0.2.0 and parity build
  passes. CLI/MCP currently provide policy discovery rather than guarded
  operational session/backport/candidate tools.
- **AC-11:** executable scenarios pass and no `.spl` exists under
  `doc/06_spec`; the manual requires regeneration after the final identity
  hardening and the documented adversarial matrix is not complete.
- **AC-13:** focused tests and plugin parity pass, but the available executable
  identifies itself as bootstrap seed-derived. Lint and the required whole
  suite therefore have no release-grade PASS.
- **AC-15:** this report deliberately leaves verification, release, and the
  thread goal incomplete.

## Independent highest-capability review

The final reviewer returned `STATUS: FAIL`. P0 findings were: legacy release
preparation bypass, caller-trusted version/receipt facts, absent
compatibility-aware bumping, incomplete adversarial/CLI/whole-suite evidence,
and stale generated manual. The direct publication dispatch and legacy prepare
mutation path were disabled after review; the remaining gaps are release
blockers, not warnings converted to PASS.

## Required next work

1. Implement repository-backed version render/check/bump and compatibility
   dimension enforcement.
2. Bind session, review, backport, candidate, admission, and promotion to exact
   verified receipts and version-matched signed tags.
3. Add guarded Spipe operational CLI/MCP tools and semantic projection hashes.
4. Convert release CI to candidate-build plus promote-only publication.
5. Regenerate and review the manual, complete adversarial CLI scenarios, then
   run lint and the whole suite with an admitted pure-Simple executable.
