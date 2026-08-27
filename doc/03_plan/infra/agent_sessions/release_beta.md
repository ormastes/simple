# Lane: 1.0.0 beta release

Goal: produce the next 1.0.0 beta from an immutable admitted candidate, with
reviewed exact bug-fix convergence, full required bootstrap/whole-test evidence,
signed promotion, and byte-identical package publication.

## Current evidence (2026-08-27)

- Audited `origin/main`: `db412eb6ec2a8ebc1f6458e82357be9258a490e5`.
- Compiler closure PR #29 merged as `c163a1e06a00644bae73d5321a1e71eb1299287a`.
- Stage-3 module-name PR #31 merged as `c01c44d7af3f756bee019f72bad413518312dc86`.
- Release-process PR #28 merged as `b76f796235031ed116a175527df50ae1e1bab1c1`.
- No remote `release/1.0` or `candidate/*` ref exists. No fresh admitted Stage 3,
  Stage 4, clean whole-suite, signed beta, immutable publication, or npm
  publication receipt exists.
- The live candidate workflow was registered under its file path and recent
  pushes produced zero-job failures. The source repair splits the oversized
  inline template and adds a regression gate, but live registration under the
  declared workflow name remains unproved until this repair reaches `main`.

## Next protected actions

1. Integrate the candidate-workflow repair, then verify that the next default-
   branch push does not create a path-named zero-job candidate run and that
   manual dispatch is registered under `Build and qualify immutable candidate`.
2. Create `release/1.0` only through the protected release-line authority.
3. Run the scheduled/operator source-hosted, fetch-only convergence observation.
   It is explicitly ineligible for release admission. For every
   operator-selected reviewed fix, use an isolated backport/forward-port session,
   stable patch-ID equivalence, renewed evidence, and protected CAS integration.
4. Qualify receipt-free Stage 2, planner-receipted Stage 3/4, version/support,
   and reviewed convergence first. Reserve the immutable candidate attempt only
   after those prerequisites pass, then promote the same assets without rebuilding.

Do not reuse the historical `release_beta_verify` Stage-2 result as current
release evidence and do not create a release line, version, or candidate from
this tracking document.
